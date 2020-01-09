use ExtUtils::MakeMaker;

my $solvprefix = '/usr';

my $inc = "-I$solvprefix/include/solv";
my $lib;

if (grep {$_ eq '--bundled-libsolv'} @ARGV) {
  my $builddir = 'libsolv';
  $inc = "-I$builddir/src -I$builddir/ext";
  $lib = "-L$builddir/src -L$builddir/ext -lsolvext -lsolv -lz -llzma -lzstd";
} else {
  $lib = '-lsolvext -lsolv';
}


WriteMakefile(
    NAME         => 'BSSolv',
    VERSION_FROM => 'BSSolv.pm',
    INC          => $inc,
    LIBS         => [ $lib ],
)
