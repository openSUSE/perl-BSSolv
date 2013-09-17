use ExtUtils::MakeMaker;

my $solvprefix = '/usr';

my $inc = "-I$solvprefix/include/solv";
my $lib = '';

if (@ARGV && $ARGV[0] eq '--bundled-libsolv') {
  my $builddir = 'libsolv';
  $inc = "-I$builddir/src -I$builddir/ext";
  $lib = "-L$builddir/src -L$builddir/ext";
}

$lib = ($lib ? "$lib " : '') . '-lsolvext -lsolv -lz -llzma';

WriteMakefile(
    NAME         => 'BSSolv',
    VERSION_FROM => 'BSSolv.pm',
    INC          => $inc,
    LIBS         => [ $lib ],
)
