#!/usr/bin/perl -w

use strict;
use Test::More tests => 2;

require 't/testlib.pm';

my $proj = {};
my $proj_maint = {'kind' => 'maintenance_release'};

my @packids = qw{foo b.1:foo c.4 a.3 z z-bar z:red z-bar:green _volatile xxxx.imported_foo_bar102 b.1};
my @result;
my @expected;

@result = BSSolv::orderpackids(0, @packids);
@expected = qw{a.3 b.1 b.1:foo c.4 foo xxxx.imported_foo_bar102 z z:red z-bar z-bar:green _volatile};
is_deeply(\@result,\@expected,"check orderpackids on standard projects");

@result = BSSolv::orderpackids(1, @packids);
@expected = qw{foo z z:red z-bar z-bar:green c.4 a.3 b.1 b.1:foo xxxx.imported_foo_bar102 _volatile};
is_deeply(\@result,\@expected,"check orderpackids on maintenance_release projects");

