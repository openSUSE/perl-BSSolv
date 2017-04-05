
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
  my $config = {};
  $config->{'expandflags'} = [];
  $config->{'prefer'} = [];
  $config->{'ignore'} = [];
  $config->{'conflict'} = [];
  for my $l (@$cfile) {
    my @l = split(' ', $l);
    next unless @l;
    my $ll = shift @l;
    my $l0 = lc($ll);
    if ($l0 eq 'prefer:' || $l0 eq 'ignore:' || $l0 eq 'conflict:' || $l0 eq 'expandflags:') {
      my $t = substr($l0, 0, -1);
      for my $l (@l) {
        push @{$config->{$t}}, $l;
      }
    } elsif ($l0 !~ /^[#%]/) {
      die("unknown keyword in config: $l0\n");
    }
  }
  $config->{'binarytype'} = 'rpm';
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
  my $packages = {};
  my $k = 0;
  for my $r (@$repo) {
    my @s = split(' ', $r);
    my $s = shift @s;
    my @ss;
    while (@s) {
      if ($s[0] =~ /^\(/) {
	push @ss, shiftrich(\@s);
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
        die unless @ss && $ss[0] =~ /^(\S+) = (\S+)(?:-(\S+))?$/;
        $packages->{$k}->{'name'} = $1;
        $packages->{$k}->{'version'} = $2;
        $packages->{$k}->{'release'} = $3 if defined $3;
      }
      $packages->{$k}->{$knowndeps{$1}} = \@ss;
    }
  }
  return $packages;
}

sub setuptest {
  my ($repo, $conf) = @_;
  my $config = read_config('noarch', [ split("\n", $conf || '') ]);
  my $pool = BSSolv::pool->new();
  $config->{'pool'} = $pool;
  $pool->repofromdata("repo", parserepo([ split("\n", $repo) ]));
  $pool->createwhatprovides();
  return $config;
}

1;
