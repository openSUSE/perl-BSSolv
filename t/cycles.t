#!/usr/bin/perl -w

use strict;
use Test::More tests => 1;

require 't/testlib.pm';

sub reach_x {
  my ($node, $edg) = @_;
  my %done;
  my @todo = $node;
  while (@todo) {
    my $n = shift @todo;
    next if $done{$n};
    $done{$n} = 1;
    push @todo, @{$edg->{$n} || []};
  }
  return [ sort keys %done ];
}

# super slow scc implementation just for testing
sub scc_x {
  my ($vert, $edg) = @_;
  my %reach;
  for my $v (sort @$vert) {
    $reach{$v}->{$_} = 1 for @{reach_x($v, $edg)}
  }
  my @sccs;
  for my $v (sort @$vert) {
    my @scc = grep {$reach{$_}->{$v}} sort keys %{$reach{$v}};
    push @sccs, \@scc if @scc > 1 && $scc[0] eq $v;
  }
  return @sccs;
}

sub depsort_x {
  my ($depsp, $mapp, $cycp, @packs) = @_;

  return @packs if @packs < 2;
  my %deps;
  my %known = map {$_ => 1} @packs;
  die("sortpacks: input not unique\n") if @packs != keys(%known);
  for my $p (@packs) {
    my @fdeps = @{$depsp->{$p} || []};
    @fdeps = map {$mapp->{$_} || $_} @fdeps if $mapp;
    @fdeps = grep {$known{$_}} @fdeps;
    my %fdeps = ($p => 1);      # no self reference
    @fdeps = grep {!$fdeps{$_}++} @fdeps;
    $deps{$p} = \@fdeps;
  }
  undef %known;         # free memory
  my @sccs = scc_x(\@packs, \%deps);
  push @$cycp, @sccs if $cycp;
}

#
# Sort packages by dependencies mapped to source packages
#
sub depsort2_x {
  my ($deps, $dep2src, $pkg2src, $cycles, @packs) = @_;
  my %src2pkg = reverse(%$pkg2src);
  my %pkgdeps;
  my @dups;
  if (keys(%src2pkg) != keys (%$pkg2src)) {
    @dups = grep {$src2pkg{$pkg2src->{$_}} ne $_} reverse(keys %$pkg2src);
  }
  if (@dups) {
    push @dups, grep {defined($_)} map {delete $src2pkg{$pkg2src->{$_}}} @dups;
    @dups = sort(@dups);
    #print "src2pkg dups: @dups\n";
    push @{$src2pkg{$pkg2src->{$_}}}, $_ for @dups;
    for my $pkg (keys %$deps) {
      $pkgdeps{$pkg} = [ map {ref($_) ? @$_ : $_} map { $src2pkg{$dep2src->{$_} || $_} || $dep2src->{$_} || $_} @{$deps->{$pkg}} ];
    }
  } else {
    for my $pkg (keys %$deps) {
      $pkgdeps{$pkg} = [ map { $src2pkg{$dep2src->{$_} || $_} || $dep2src->{$_} || $_} @{$deps->{$pkg}} ];
    }
  }
  return depsort_x(\%pkgdeps, undef, $cycles, @packs);
}

BSSolv::setdepsortsccs(1);

my @cycles_x;
my @cycles;

#use Storable;
#my $hashref = retrieve('t/state.home:coolo:bootstrap-test');
#depsort2_x($hashref->{pdeps}, $hashref->{dep2src}, $hashref->{pkg2src}, \@cycles_x, @{$hashref->{packs}});
#BSSolv::depsort2($hashref->{pdeps}, $hashref->{dep2src}, $hashref->{pkg2src}, \@cycles, @{$hashref->{packs}});
#@$_ = sort @$_ for @cycles;
#@cycles = sort {$a->[0] cmp $b->[0]} @cycles;
#is_deeply(\@cycles, \@cycles_x, 'scc calculation with bootstrap testdata');

srand(7);
my @nodes = ("0000" .. "9999");
my %edges;
my $fill = int(1 * scalar(@nodes));
for (my $i = 0; $i < $fill; $i++) {
  my $start = $nodes[int(rand(scalar(@nodes)))];
  my $end = $nodes[int(rand(scalar(@nodes)))];
  $edges{$start}->{$end} = 1 unless $start eq $end;
}
$edges{$_} = [ sort keys %{$edges{$_} || {}} ] for @nodes;
my %ident = map {$_ => $_} @nodes;

@cycles = ();
@cycles_x = ();
depsort2_x(\%edges, \%ident, \%ident, \@cycles_x, @nodes);
BSSolv::depsort2(\%edges, \%ident, \%ident, \@cycles, @nodes);
@$_ = sort @$_ for @cycles;
@cycles = sort {$a->[0] cmp $b->[0]} @cycles;
is_deeply(\@cycles, \@cycles_x, 'scc calculation with random testdata');
