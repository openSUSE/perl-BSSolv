package BSSolv;

use strict;

require Exporter;

our @ISA = qw(Exporter);

our $VERSION = '0.09';

require XSLoader;

XSLoader::load('BSSolv', $VERSION);

package BSSolv::repo;

1;
