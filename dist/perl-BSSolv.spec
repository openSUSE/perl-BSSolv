#
# spec file for package perl-BSSolv
#
# Copyright (c) 2016 SUSE LINUX GmbH, Nuernberg, Germany.
#
# All modifications and additions to the file contributed by third parties
# remain the property of their copyright owners, unless otherwise agreed
# upon. The license for this file, and modifications and additions to the
# file, is the same license as for the pristine package itself (unless the
# license for the pristine package is not an Open Source License, in which
# case the license is the MIT License). An "Open Source License" is a
# license that conforms to the Open Source Definition (Version 1.9)
# published by the Open Source Initiative.

# Please submit bugfixes or comments via http://bugs.opensuse.org/
#


Name:           perl-BSSolv
Version:        0.33.0
Release:        0
Url:            https://github.com/openSUSE/perl-BSSolv
Source:         libsolv-0.6.27.tar.gz
Source1:        Makefile.PL
Source2:        BSSolv.pm
Source3:        BSSolv.xs
Source4:        typemap
BuildRoot:      %{_tmppath}/%{name}-%{version}-build

%if 0%{?fedora_version}
BuildRequires:  perl-devel
%endif
%if 0%{?suse_version}
Requires:       perl = %perl_version
%endif
BuildRequires:  cmake
BuildRequires:  gcc-c++
BuildRequires:  perl
BuildRequires:  xz-devel
BuildRequires:  zlib-devel
#RHEL6 moved ExtUtils::MakeMaker outside the main perl package
BuildRequires:  perl(ExtUtils::MakeMaker)
# the testsuite uses the check framework
BuildRequires:  check-devel
Summary:        A new approach to package dependency solving
License:        BSD-3-Clause
Group:          Development/Libraries/C and C++
# probably needed for rhel/centos on x86_64
%if 0%{!?perl_vendorarch}
%define perl_vendorarch %(eval "`%{__perl} -V:installvendorarch`"; echo $installvendorarch)
%endif

%description
Using a Satisfyability Solver to compute package dependencies.

%prep
%setup -c
ln -s libsolv-* libsolv
cp %{SOURCE1} %{SOURCE2} %{SOURCE3} %{SOURCE4} .
pushd libsolv
popd

%build
export CFLAGS="$RPM_OPT_FLAGS"
export CXXFLAGS="$CFLAGS"

CMAKE_FLAGS=
%if 0%{?rhel_version} || 0%{?centos_version}
CFLAGS="$CFLAGS -DUSE_OWN_QSORT"
%endif

pushd libsolv
cmake   $CMAKE_FLAGS \
	-DDISABLE_SHARED=1 \
	-DCMAKE_BUILD_TYPE=Release \
	-DCMAKE_SKIP_RPATH=1 \
	-DENABLE_RPMPKG=1 \
	-DENABLE_DEBIAN=1 \
	-DENABLE_ARCHREPO=1 \
	-DENABLE_LZMA_COMPRESSION=1 \
	-DENABLE_COMPLEX_DEPS=1 \
	-DMULTI_SEMANTICS=1
pushd src ; make ; popd
pushd ext ; make ; popd
popd

perl Makefile.PL --bundled-libsolv
make

%check
make test

%install
make DESTDIR=$RPM_BUILD_ROOT install_vendor
%if 0%{?suse_version}  
%perl_process_packlist  
%else  
find $RPM_BUILD_ROOT -type f -name perllocal.pod -exec rm -f {} \;  
find $RPM_BUILD_ROOT -type f -name .packlist -exec rm -f {} \;  
find $RPM_BUILD_ROOT -type f -name '*.bs' -a -size 0 -exec rm -f {} ';'  
find $RPM_BUILD_ROOT -depth -type d -exec rmdir {} 2>/dev/null \;  
%{_fixperms} $RPM_BUILD_ROOT/*  
%endif  

%files
%defattr(-,root,root)
%{perl_vendorarch}/BSSolv.pm
%{perl_vendorarch}/auto/BSSolv
%if 0%{?suse_version}
%if 0%{?suse_version} < 1140
/var/adm/perl-modules/*
%endif
%endif

%changelog
