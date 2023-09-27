
use BSSolv;
use strict;

sub expand {
  my ($config, @job) = @_;
  my $pool = $config->{'pool'};
  my $xp = BSSolv::expander->new($pool, $config);
  my ($c, @r) = $xp->expand(@job);
  return ($c, sort(@r));
}

# dummy version of Build's read_config
sub read_config {
  my ($arch, $cfile) = @_;
  my $config = { 'binarytype' => 'rpm' };
  $config->{$_} = [] for qw{prefer ignore conflict expandflags};
  for my $l (@$cfile) {
    my @l = split(' ', $l);
    next unless @l;
    my $ll = shift @l;
    my $l0 = lc($ll);
    if ($l0 eq 'prefer:' || $l0 eq 'ignore:' || $l0 eq 'conflict:' || $l0 eq 'expandflags:') {
      push @{$config->{substr($l0, 0, -1)}}, @l;
    } elsif ($l0 eq 'binarytype:') {
      $config->{'binarytype'} = $l[0];
    } elsif ($l0 eq 'fileprovides:') {
      my $f = shift @l;
      push @{$config->{'fileprovides'}->{$f}}, @l;
    } elsif ($l0 !~ /^[#%]/) {
      die("unknown keyword in config: $l0\n");
    }
  }
  $config->{'ignoreh'} = {};
  for (@{$config->{'ignore'}}) {
    if (!/:/) {
      $config->{'ignoreh'}->{$_} = 1; 
      next;
    }
    my @s = split(/[,:]/, $_); 
    my $s = shift @s;
    $config->{'ignoreh'}->{"$s:$_"} = 1 for @s;
  }
  for (@{$config->{'expandflags'} || []}) {
    if (/^([^:]+):(.*)$/s) {
      $config->{"expandflags:$1"} = $2;
    } else {
      $config->{"expandflags:$_"} = 1;
    }
  }
  return $config;
}

sub shiftrich {
  my ($s) = @_;
  # FIXME: do this right!
  my $dep = shift @$s;
  while (@$s && ($dep =~ y/\(/\(/) > ($dep =~ y/\)/\)/)) {
    $dep .= ' ' . shift(@$s); 
  }
  return $dep;
}

my %knowndeps = ('P' => 'provides', 'R' => 'requires', 'C' => 'conflicts', 'O' => 'obsoletes',
                 'r' => 'recommends', 's' => 'supplements');

sub parserepo {
  my ($repo) = @_;
  my @packages;
  my $k = 0;
  for my $r (@$repo) {
    my @s = split(' ', $r);
    my $s = shift @s;
    my @ss;
    while (@s) {
      if ($s[0] =~ /^\(/) {
	push @ss, shiftrich(\@s);
	$ss[-1] =~ s/ if / <IF> /g;
	$ss[-1] =~ s/ else / <ELSE> /g;
	$ss[-1] =~ s/ unless / <UNLESS> /g;
	$ss[-1] =~ s/ and / & /g;
	$ss[-1] =~ s/ or / | /g;
	next;
      }
      push @ss, shift @s;
      while (@s && $s[0] =~ /^[\(<=>|]/) {
        $ss[-1] .= " $s[0] $s[1]";
        $ss[-1] =~ s/ \((.*)\)/ $1/;
        $ss[-1] =~ s/(<|>){2}/$1/;
        splice(@s, 0, 2);
      }
    }
    if ($s =~ /^(P|R|C|O|r|s):/) {
      if ($1 eq 'P') {
	$k++;
        die unless @ss && $ss[0] =~ /^(\S+) = (\S+?)(?:-(\S+))?$/;
        push @packages, {'name' => $1, 'version' => $2};
        $packages[-1]->{'release'} = $3 if defined $3;
      }
      $packages[-1]->{$knowndeps{$1}} = \@ss;
    } elsif ($s =~ /^M:/) {
      $packages[-1]->{'multiarch'} = $ss[0]
    }
  }
  #@packages = reverse @packages;
  return \@packages;
}

sub setuptest {
  my ($repo, $conf) = @_;
  my $config = read_config('noarch', [ split("\n", $conf || '') ]);
  my $pool = BSSolv::pool->new();
  $pool->settype('deb') if $config->{'binarytype'} eq 'deb';
  $config->{'pool'} = $pool;
  $pool->repofromdata("repo", parserepo([ split("\n", $repo) ]));
  $pool->createwhatprovides();
  return $config;
}

1;
