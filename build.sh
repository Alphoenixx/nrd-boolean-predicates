#!/usr/bin/env sh
# Build every executable. CXX and CXXFLAGS are honoured.
set -e
CXX="${CXX:-g++}"
CXXFLAGS="${CXXFLAGS:--O2}"
STD="-std=c++20"
WARN="-Wall -Wextra"

$CXX $STD $CXXFLAGS $WARN -Isrc/classification -o bin_test    tests/test_nrd.cpp
$CXX $STD $CXXFLAGS $WARN -Isrc/classification -o bin_testx   tests/test_nrdx.cpp
$CXX $STD $CXXFLAGS $WARN -Isrc/classification -o bin_sweep   src/classification/sweep.cpp
$CXX $STD $CXXFLAGS $WARN -Isrc/classification -o bin_est     src/classification/estimate.cpp
$CXX $STD $CXXFLAGS $WARN -Isrc/classification -o bin_search  src/classification/search.cpp
$CXX $STD $CXXFLAGS $WARN -Isrc/classification -o bin_analyze src/classification/analyze.cpp

mkdir -p bin
$CXX -std=c++17 $CXXFLAGS -Isrc/gadget -o bin/wsearch  src/gadget/search.cpp  -pthread
$CXX -std=c++17 $CXXFLAGS -Isrc/gadget -o bin/wrealize src/gadget/realize.cpp -pthread

echo "built bin_test bin_testx bin_sweep bin_est bin_search bin_analyze bin/wsearch bin/wrealize"
echo "run ./bin_test and ./bin_testx first; both must print ALL PASS"
