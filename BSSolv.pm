package BSSolv;

use strict;

require Exporter;

our @ISA = qw(Exporter);

our $VERSION = '0.07';

require XSLoader;

XSLoader::load('BSSolv', $VERSION);

package BSSolv::repo;

1;
