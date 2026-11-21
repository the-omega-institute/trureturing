/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Main04
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main04.chunk_checked
   digest: Exact numerical and binary coverage certificate for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainSupport

/-! Opaque numerical subproofs bound temporary kernel reduction memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.Main04

private abbrev C (lo hi : Fin 7 → ℕ) (tree : MainTree) : Prop :=
  checkExponentBoxTree mainScale boxPrimes lo hi tree = true

/-- Lower exponents at this subtree root. -/
def lo : Fin 7 → ℕ := ![4, 0, 0, 0, 0, 0, 0]

/-- Upper exponents at the same root. -/
def hi : Fin 7 → ℕ := ![17, 1, 1, 2, 1, 1, 1]

private def n1809 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 0, 0, 0, 0])
private def n1810 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 0, 0, 0, 1])
private def n1808 : MainTree := .split 6 0 n1809 n1810
private def n1812 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 0, 0, 1, 0])
private def n1813 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 0, 0, 1, 1])
private def n1811 : MainTree := .split 6 0 n1812 n1813
private def n1807 : MainTree := .split 5 0 n1808 n1811
private def n1816 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 0, 1, 0, 0])
private def n1817 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 0, 1, 0, 1])
private def n1815 : MainTree := .split 6 0 n1816 n1817
private def n1819 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 0, 1, 1, 0])
private def n1820 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 0, 1, 1, 1])
private def n1818 : MainTree := .split 6 0 n1819 n1820
private def n1814 : MainTree := .split 5 0 n1815 n1818
private def n1806 : MainTree := .split 4 0 n1807 n1814
private def n1824 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 0, 0, 0, 0])
private def n1825 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 0, 0, 0, 1])
private def n1823 : MainTree := .split 6 0 n1824 n1825
private def n1827 : MainTree := .leaf (mainRankLeaf 1 ![8, 0, 1, 0, 0, 1, 0])
private def n1828 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 0, 0, 1, 1])
private def n1826 : MainTree := .split 6 0 n1827 n1828
private def n1822 : MainTree := .split 5 0 n1823 n1826
private def n1831 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 0, 1, 0, 0])
private def n1832 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 0, 1, 0, 1])
private def n1830 : MainTree := .split 6 0 n1831 n1832
private def n1834 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 0, 1, 1, 0])
private def n1835 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 0, 1, 1, 1])
private def n1833 : MainTree := .split 6 0 n1834 n1835
private def n1829 : MainTree := .split 5 0 n1830 n1833
private def n1821 : MainTree := .split 4 0 n1822 n1829
private def n1805 : MainTree := .split 2 0 n1806 n1821
private def n1842 : MainTree := .leaf (mainGapLeaf ![4, 1, 0, 0, 0, 0, 0])
private def n1843 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 0, 0, 0, 0])
private def n1841 : MainTree := .split 0 4 n1842 n1843
private def n1844 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 0, 0, 0, 0])
private def n1840 : MainTree := .split 0 5 n1841 n1844
private def n1846 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 0, 0, 0, 1])
private def n1847 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 0, 0, 0, 1])
private def n1845 : MainTree := .split 0 5 n1846 n1847
private def n1839 : MainTree := .split 6 0 n1840 n1845
private def n1850 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 0, 0, 1, 0])
private def n1851 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 0, 0, 1, 0])
private def n1849 : MainTree := .split 0 5 n1850 n1851
private def n1852 : MainTree := .leaf (mainRankLeaf 1 ![8, 1, 0, 0, 0, 1, 1])
private def n1848 : MainTree := .split 6 0 n1849 n1852
private def n1838 : MainTree := .split 5 0 n1839 n1848
private def n1857 : MainTree := .leaf (mainGapLeaf ![4, 1, 0, 0, 1, 0, 0])
private def n1858 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 0, 1, 0, 0])
private def n1856 : MainTree := .split 0 4 n1857 n1858
private def n1859 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 0, 1, 0, 0])
private def n1855 : MainTree := .split 0 5 n1856 n1859
private def n1861 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 0, 1, 0, 1])
private def n1862 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 0, 1, 0, 1])
private def n1860 : MainTree := .split 0 5 n1861 n1862
private def n1854 : MainTree := .split 6 0 n1855 n1860
private def n1865 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 0, 1, 1, 0])
private def n1866 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 0, 1, 1, 0])
private def n1864 : MainTree := .split 0 5 n1865 n1866
private def n1867 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 0, 1, 1, 1])
private def n1863 : MainTree := .split 6 0 n1864 n1867
private def n1853 : MainTree := .split 5 0 n1854 n1863
private def n1837 : MainTree := .split 4 0 n1838 n1853
private def n1873 : MainTree := .leaf (mainFullLeaf ![4, 1, 1, 0, 0, 0, 0])
private def n1874 : MainTree := .leaf (mainFullLeaf ![5, 1, 1, 0, 0, 0, 0])
private def n1872 : MainTree := .split 0 4 n1873 n1874
private def n1876 : MainTree := .leaf (mainRankLeaf 2 ![6, 1, 1, 0, 0, 0, 0])
private def n1877 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 0, 0, 0, 0])
private def n1875 : MainTree := .split 0 6 n1876 n1877
private def n1871 : MainTree := .split 0 5 n1872 n1875
private def n1880 : MainTree := .leaf (mainGapLeaf ![4, 1, 1, 0, 0, 0, 1])
private def n1881 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 0, 0, 0, 1])
private def n1879 : MainTree := .split 0 4 n1880 n1881
private def n1882 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 0, 0, 0, 1])
private def n1878 : MainTree := .split 0 5 n1879 n1882
private def n1870 : MainTree := .split 6 0 n1871 n1878
private def n1886 : MainTree := .leaf (mainRankLeaf 2 ![4, 1, 1, 0, 0, 1, 0])
private def n1887 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 0, 0, 1, 0])
private def n1885 : MainTree := .split 0 4 n1886 n1887
private def n1889 : MainTree := .leaf (mainGapLeaf ![6, 1, 1, 0, 0, 1, 0])
private def n1890 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 0, 0, 1, 0])
private def n1888 : MainTree := .split 0 6 n1889 n1890
private def n1884 : MainTree := .split 0 5 n1885 n1888
private def n1892 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 0, 0, 1, 1])
private def n1893 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 0, 0, 1, 1])
private def n1891 : MainTree := .split 0 5 n1892 n1893
private def n1883 : MainTree := .split 6 0 n1884 n1891
private def n1869 : MainTree := .split 5 0 n1870 n1883
private def n1898 : MainTree := .leaf (mainRankLeaf 2 ![4, 1, 1, 0, 1, 0, 0])
private def n1899 : MainTree := .leaf (mainRankLeaf 2 ![5, 1, 1, 0, 1, 0, 0])
private def n1897 : MainTree := .split 0 4 n1898 n1899
private def n1901 : MainTree := .leaf (mainGapLeaf ![6, 1, 1, 0, 1, 0, 0])
private def n1902 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 0, 1, 0, 0])
private def n1900 : MainTree := .split 0 6 n1901 n1902
private def n1896 : MainTree := .split 0 5 n1897 n1900
private def n1904 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 0, 1, 0, 1])
private def n1905 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 0, 1, 0, 1])
private def n1903 : MainTree := .split 0 5 n1904 n1905
private def n1895 : MainTree := .split 6 0 n1896 n1903
private def n1909 : MainTree := .leaf (mainGapLeaf ![4, 1, 1, 0, 1, 1, 0])
private def n1910 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 0, 1, 1, 0])
private def n1908 : MainTree := .split 0 4 n1909 n1910
private def n1911 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 0, 1, 1, 0])
private def n1907 : MainTree := .split 0 5 n1908 n1911
private def n1912 : MainTree := .leaf (mainRankLeaf 1 ![8, 1, 1, 0, 1, 1, 1])
private def n1906 : MainTree := .split 6 0 n1907 n1912
private def n1894 : MainTree := .split 5 0 n1895 n1906
private def n1868 : MainTree := .split 4 0 n1869 n1894
private def n1836 : MainTree := .split 2 0 n1837 n1868
private def n1804 : MainTree := .split 1 0 n1805 n1836
private def n1919 : MainTree := .leaf (mainRankLeaf 1 ![5, 0, 0, 2, 0, 0, 0])
private def n1920 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 2, 0, 0, 0])
private def n1918 : MainTree := .split 0 5 n1919 n1920
private def n1921 : MainTree := .leaf (mainRankLeaf 1 ![8, 0, 0, 2, 0, 0, 1])
private def n1917 : MainTree := .split 6 0 n1918 n1921
private def n1924 : MainTree := .leaf (mainRankLeaf 1 ![5, 0, 0, 2, 0, 1, 0])
private def n1925 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 2, 0, 1, 0])
private def n1923 : MainTree := .split 0 5 n1924 n1925
private def n1926 : MainTree := .leaf (mainRankLeaf 1 ![8, 0, 0, 2, 0, 1, 1])
private def n1922 : MainTree := .split 6 0 n1923 n1926
private def n1916 : MainTree := .split 5 0 n1917 n1922
private def n1929 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 2, 1, 0, 0])
private def n1930 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 2, 1, 0, 1])
private def n1928 : MainTree := .split 6 0 n1929 n1930
private def n1932 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 2, 1, 1, 0])
private def n1933 : MainTree := .leaf (mainGapLeaf ![8, 0, 0, 2, 1, 1, 1])
private def n1931 : MainTree := .split 6 0 n1932 n1933
private def n1927 : MainTree := .split 5 0 n1928 n1931
private def n1915 : MainTree := .split 4 0 n1916 n1927
private def n1939 : MainTree := .leaf (mainGapLeaf ![5, 0, 1, 1, 0, 0, 0])
private def n1940 : MainTree := .leaf (mainGapLeaf ![5, 0, 1, 2, 0, 0, 0])
private def n1938 : MainTree := .split 3 1 n1939 n1940
private def n1941 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 2, 0, 0, 0])
private def n1937 : MainTree := .split 0 5 n1938 n1941
private def n1943 : MainTree := .leaf (mainGapLeaf ![5, 0, 1, 2, 0, 0, 1])
private def n1944 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 2, 0, 0, 1])
private def n1942 : MainTree := .split 0 5 n1943 n1944
private def n1936 : MainTree := .split 6 0 n1937 n1942
private def n1947 : MainTree := .leaf (mainGapLeaf ![5, 0, 1, 2, 0, 1, 0])
private def n1948 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 2, 0, 1, 0])
private def n1946 : MainTree := .split 0 5 n1947 n1948
private def n1949 : MainTree := .leaf (mainRankLeaf 1 ![8, 0, 1, 2, 0, 1, 1])
private def n1945 : MainTree := .split 6 0 n1946 n1949
private def n1935 : MainTree := .split 5 0 n1936 n1945
private def n1954 : MainTree := .leaf (mainGapLeaf ![5, 0, 1, 1, 1, 0, 0])
private def n1955 : MainTree := .leaf (mainGapLeaf ![5, 0, 1, 2, 1, 0, 0])
private def n1953 : MainTree := .split 3 1 n1954 n1955
private def n1956 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 2, 1, 0, 0])
private def n1952 : MainTree := .split 0 5 n1953 n1956
private def n1957 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 2, 1, 0, 1])
private def n1951 : MainTree := .split 6 0 n1952 n1957
private def n1960 : MainTree := .leaf (mainGapLeaf ![5, 0, 1, 2, 1, 1, 0])
private def n1961 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 2, 1, 1, 0])
private def n1959 : MainTree := .split 0 5 n1960 n1961
private def n1962 : MainTree := .leaf (mainGapLeaf ![8, 0, 1, 2, 1, 1, 1])
private def n1958 : MainTree := .split 6 0 n1959 n1962
private def n1950 : MainTree := .split 5 0 n1951 n1958
private def n1934 : MainTree := .split 4 0 n1935 n1950
private def n1914 : MainTree := .split 2 0 n1915 n1934
private def n1970 : MainTree := .leaf (mainRankLeaf 2 ![4, 1, 0, 1, 0, 0, 0])
private def n1971 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 1, 0, 0, 0])
private def n1969 : MainTree := .split 0 4 n1970 n1971
private def n1973 : MainTree := .leaf (mainGapLeaf ![4, 1, 0, 2, 0, 0, 0])
private def n1974 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 2, 0, 0, 0])
private def n1972 : MainTree := .split 0 4 n1973 n1974
private def n1968 : MainTree := .split 3 1 n1969 n1972
private def n1976 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 1, 0, 0, 0])
private def n1977 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 2, 0, 0, 0])
private def n1975 : MainTree := .split 3 1 n1976 n1977
private def n1967 : MainTree := .split 0 5 n1968 n1975
private def n1980 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 1, 0, 0, 1])
private def n1981 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 2, 0, 0, 1])
private def n1979 : MainTree := .split 3 1 n1980 n1981
private def n1982 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 2, 0, 0, 1])
private def n1978 : MainTree := .split 0 5 n1979 n1982
private def n1966 : MainTree := .split 6 0 n1967 n1978
private def n1987 : MainTree := .leaf (mainGapLeaf ![4, 1, 0, 1, 0, 1, 0])
private def n1988 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 1, 0, 1, 0])
private def n1986 : MainTree := .split 0 4 n1987 n1988
private def n1989 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 2, 0, 1, 0])
private def n1985 : MainTree := .split 3 1 n1986 n1989
private def n1991 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 1, 0, 1, 0])
private def n1992 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 2, 0, 1, 0])
private def n1990 : MainTree := .split 3 1 n1991 n1992
private def n1984 : MainTree := .split 0 5 n1985 n1990
private def n1995 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 1, 0, 1, 1])
private def n1996 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 2, 0, 1, 1])
private def n1994 : MainTree := .split 3 1 n1995 n1996
private def n1997 : MainTree := .leaf (mainRankLeaf 1 ![8, 1, 0, 2, 0, 1, 1])
private def n1993 : MainTree := .split 0 5 n1994 n1997
private def n1983 : MainTree := .split 6 0 n1984 n1993
private def n1965 : MainTree := .split 5 0 n1966 n1983
private def n2003 : MainTree := .leaf (mainGapLeaf ![4, 1, 0, 1, 1, 0, 0])
private def n2004 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 1, 1, 0, 0])
private def n2002 : MainTree := .split 0 4 n2003 n2004
private def n2005 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 2, 1, 0, 0])
private def n2001 : MainTree := .split 3 1 n2002 n2005
private def n2007 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 1, 1, 0, 0])
private def n2008 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 2, 1, 0, 0])
private def n2006 : MainTree := .split 3 1 n2007 n2008
private def n2000 : MainTree := .split 0 5 n2001 n2006
private def n2011 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 1, 1, 0, 1])
private def n2012 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 2, 1, 0, 1])
private def n2010 : MainTree := .split 3 1 n2011 n2012
private def n2013 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 2, 1, 0, 1])
private def n2009 : MainTree := .split 0 5 n2010 n2013
private def n1999 : MainTree := .split 6 0 n2000 n2009
private def n2017 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 1, 1, 1, 0])
private def n2018 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 2, 1, 1, 0])
private def n2016 : MainTree := .split 3 1 n2017 n2018
private def n2019 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 2, 1, 1, 0])
private def n2015 : MainTree := .split 0 5 n2016 n2019
private def n2021 : MainTree := .leaf (mainGapLeaf ![5, 1, 0, 2, 1, 1, 1])
private def n2022 : MainTree := .leaf (mainGapLeaf ![8, 1, 0, 2, 1, 1, 1])
private def n2020 : MainTree := .split 0 5 n2021 n2022
private def n2014 : MainTree := .split 6 0 n2015 n2020
private def n1998 : MainTree := .split 5 0 n1999 n2014
private def n1964 : MainTree := .split 4 0 n1965 n1998
private def n2029 : MainTree := .leaf (mainFullLeaf ![4, 1, 1, 1, 0, 0, 0])
private def n2030 : MainTree := .leaf (mainFullLeaf ![5, 1, 1, 1, 0, 0, 0])
private def n2028 : MainTree := .split 0 4 n2029 n2030
private def n2032 : MainTree := .leaf (mainGapLeaf ![4, 1, 1, 2, 0, 0, 0])
private def n2033 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 2, 0, 0, 0])
private def n2031 : MainTree := .split 0 4 n2032 n2033
private def n2027 : MainTree := .split 3 1 n2028 n2031
private def n2036 : MainTree := .leaf (mainRankLeaf 2 ![6, 1, 1, 1, 0, 0, 0])
private def n2037 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 1, 0, 0, 0])
private def n2035 : MainTree := .split 0 6 n2036 n2037
private def n2038 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 2, 0, 0, 0])
private def n2034 : MainTree := .split 3 1 n2035 n2038
private def n2026 : MainTree := .split 0 5 n2027 n2034
private def n2042 : MainTree := .leaf (mainRankLeaf 2 ![4, 1, 1, 1, 0, 0, 1])
private def n2043 : MainTree := .leaf (mainRankLeaf 1 ![5, 1, 1, 1, 0, 0, 1])
private def n2041 : MainTree := .split 0 4 n2042 n2043
private def n2044 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 2, 0, 0, 1])
private def n2040 : MainTree := .split 3 1 n2041 n2044
private def n2046 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 1, 0, 0, 1])
private def n2047 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 2, 0, 0, 1])
private def n2045 : MainTree := .split 3 1 n2046 n2047
private def n2039 : MainTree := .split 0 5 n2040 n2045
private def n2025 : MainTree := .split 6 0 n2026 n2039
private def n2052 : MainTree := .leaf (mainRankLeaf 2 ![4, 1, 1, 1, 0, 1, 0])
private def n2053 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 1, 0, 1, 0])
private def n2051 : MainTree := .split 0 4 n2052 n2053
private def n2054 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 2, 0, 1, 0])
private def n2050 : MainTree := .split 3 1 n2051 n2054
private def n2057 : MainTree := .leaf (mainGapLeaf ![6, 1, 1, 1, 0, 1, 0])
private def n2058 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 1, 0, 1, 0])
private def n2056 : MainTree := .split 0 6 n2057 n2058
private def n2059 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 2, 0, 1, 0])
private def n2055 : MainTree := .split 3 1 n2056 n2059
private def n2049 : MainTree := .split 0 5 n2050 n2055
private def n2062 : MainTree := .leaf (mainRankLeaf 1 ![5, 1, 1, 1, 0, 1, 1])
private def n2063 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 2, 0, 1, 1])
private def n2061 : MainTree := .split 3 1 n2062 n2063
private def n2065 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 1, 0, 1, 1])
private def n2066 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 2, 0, 1, 1])
private def n2064 : MainTree := .split 3 1 n2065 n2066
private def n2060 : MainTree := .split 0 5 n2061 n2064
private def n2048 : MainTree := .split 6 0 n2049 n2060
private def n2024 : MainTree := .split 5 0 n2025 n2048
private def n2072 : MainTree := .leaf (mainFullLeaf ![4, 1, 1, 1, 1, 0, 0])
private def n2073 : MainTree := .leaf (mainRankLeaf 2 ![5, 1, 1, 1, 1, 0, 0])
private def n2071 : MainTree := .split 0 4 n2072 n2073
private def n2074 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 2, 1, 0, 0])
private def n2070 : MainTree := .split 3 1 n2071 n2074
private def n2077 : MainTree := .leaf (mainGapLeaf ![6, 1, 1, 1, 1, 0, 0])
private def n2078 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 1, 1, 0, 0])
private def n2076 : MainTree := .split 0 6 n2077 n2078
private def n2079 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 2, 1, 0, 0])
private def n2075 : MainTree := .split 3 1 n2076 n2079
private def n2069 : MainTree := .split 0 5 n2070 n2075
private def n2083 : MainTree := .leaf (mainGapLeaf ![4, 1, 1, 1, 1, 0, 1])
private def n2084 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 1, 1, 0, 1])
private def n2082 : MainTree := .split 0 4 n2083 n2084
private def n2085 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 2, 1, 0, 1])
private def n2081 : MainTree := .split 3 1 n2082 n2085
private def n2087 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 1, 1, 0, 1])
private def n2088 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 2, 1, 0, 1])
private def n2086 : MainTree := .split 3 1 n2087 n2088
private def n2080 : MainTree := .split 0 5 n2081 n2086
private def n2068 : MainTree := .split 6 0 n2069 n2080
private def n2093 : MainTree := .leaf (mainGapLeaf ![4, 1, 1, 1, 1, 1, 0])
private def n2094 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 1, 1, 1, 0])
private def n2092 : MainTree := .split 0 4 n2093 n2094
private def n2095 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 2, 1, 1, 0])
private def n2091 : MainTree := .split 3 1 n2092 n2095
private def n2097 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 1, 1, 1, 0])
private def n2098 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 2, 1, 1, 0])
private def n2096 : MainTree := .split 3 1 n2097 n2098
private def n2090 : MainTree := .split 0 5 n2091 n2096
private def n2101 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 1, 1, 1, 1])
private def n2102 : MainTree := .leaf (mainGapLeaf ![5, 1, 1, 2, 1, 1, 1])
private def n2100 : MainTree := .split 3 1 n2101 n2102
private def n2103 : MainTree := .leaf (mainGapLeaf ![8, 1, 1, 2, 1, 1, 1])
private def n2099 : MainTree := .split 0 5 n2100 n2103
private def n2089 : MainTree := .split 6 0 n2090 n2099
private def n2067 : MainTree := .split 5 0 n2068 n2089
private def n2023 : MainTree := .split 4 0 n2024 n2067
private def n1963 : MainTree := .split 2 0 n1964 n2023
private def n1913 : MainTree := .split 1 0 n1914 n1963
private def n1803 : MainTree := .split 3 0 n1804 n1913
private def n2109 : MainTree := .leaf (mainRankLeaf 1 ![17, 0, 0, 0, 0, 0, 1])
private def n2110 : MainTree := .leaf (mainGapLeaf ![17, 0, 0, 0, 0, 1, 1])
private def n2108 : MainTree := .split 5 0 n2109 n2110
private def n2112 : MainTree := .leaf (mainGapLeaf ![17, 0, 0, 0, 1, 0, 1])
private def n2113 : MainTree := .leaf (mainGapLeaf ![17, 0, 0, 0, 1, 1, 1])
private def n2111 : MainTree := .split 5 0 n2112 n2113
private def n2107 : MainTree := .split 4 0 n2108 n2111
private def n2116 : MainTree := .leaf (mainRankLeaf 1 ![17, 0, 1, 0, 0, 0, 1])
private def n2117 : MainTree := .leaf (mainGapLeaf ![17, 0, 1, 0, 0, 1, 1])
private def n2115 : MainTree := .split 5 0 n2116 n2117
private def n2119 : MainTree := .leaf (mainGapLeaf ![17, 0, 1, 0, 1, 0, 1])
private def n2120 : MainTree := .leaf (mainGapLeaf ![17, 0, 1, 0, 1, 1, 1])
private def n2118 : MainTree := .split 5 0 n2119 n2120
private def n2114 : MainTree := .split 4 0 n2115 n2118
private def n2106 : MainTree := .split 2 0 n2107 n2114
private def n2125 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 0, 0, 0, 0])
private def n2126 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 0, 0, 0, 1])
private def n2124 : MainTree := .split 6 0 n2125 n2126
private def n2127 : MainTree := .leaf (mainRankLeaf 1 ![17, 1, 0, 0, 0, 1, 1])
private def n2123 : MainTree := .split 5 0 n2124 n2127
private def n2130 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 0, 1, 0, 0])
private def n2131 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 0, 1, 0, 1])
private def n2129 : MainTree := .split 6 0 n2130 n2131
private def n2132 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 0, 1, 1, 1])
private def n2128 : MainTree := .split 5 0 n2129 n2132
private def n2122 : MainTree := .split 4 0 n2123 n2128
private def n2136 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 0, 0, 0, 0])
private def n2137 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 0, 0, 0, 1])
private def n2135 : MainTree := .split 6 0 n2136 n2137
private def n2139 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 0, 0, 1, 0])
private def n2140 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 0, 0, 1, 1])
private def n2138 : MainTree := .split 6 0 n2139 n2140
private def n2134 : MainTree := .split 5 0 n2135 n2138
private def n2143 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 0, 1, 0, 0])
private def n2144 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 0, 1, 0, 1])
private def n2142 : MainTree := .split 6 0 n2143 n2144
private def n2146 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 0, 1, 1, 0])
private def n2147 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 0, 1, 1, 1])
private def n2145 : MainTree := .split 6 0 n2146 n2147
private def n2141 : MainTree := .split 5 0 n2142 n2145
private def n2133 : MainTree := .split 4 0 n2134 n2141
private def n2121 : MainTree := .split 2 0 n2122 n2133
private def n2105 : MainTree := .split 1 0 n2106 n2121
private def n2152 : MainTree := .leaf (mainRankLeaf 1 ![17, 0, 0, 2, 0, 0, 1])
private def n2153 : MainTree := .leaf (mainRankLeaf 1 ![17, 0, 0, 2, 0, 1, 1])
private def n2151 : MainTree := .split 5 0 n2152 n2153
private def n2155 : MainTree := .leaf (mainGapLeaf ![17, 0, 0, 2, 1, 0, 1])
private def n2156 : MainTree := .leaf (mainGapLeaf ![17, 0, 0, 2, 1, 1, 1])
private def n2154 : MainTree := .split 5 0 n2155 n2156
private def n2150 : MainTree := .split 4 0 n2151 n2154
private def n2160 : MainTree := .leaf (mainGapLeaf ![17, 0, 1, 2, 0, 0, 0])
private def n2161 : MainTree := .leaf (mainGapLeaf ![17, 0, 1, 2, 0, 0, 1])
private def n2159 : MainTree := .split 6 0 n2160 n2161
private def n2163 : MainTree := .leaf (mainGapLeaf ![17, 0, 1, 2, 0, 1, 0])
private def n2164 : MainTree := .leaf (mainGapLeaf ![17, 0, 1, 2, 0, 1, 1])
private def n2162 : MainTree := .split 6 0 n2163 n2164
private def n2158 : MainTree := .split 5 0 n2159 n2162
private def n2167 : MainTree := .leaf (mainGapLeaf ![17, 0, 1, 2, 1, 0, 0])
private def n2168 : MainTree := .leaf (mainGapLeaf ![17, 0, 1, 2, 1, 0, 1])
private def n2166 : MainTree := .split 6 0 n2167 n2168
private def n2169 : MainTree := .leaf (mainGapLeaf ![17, 0, 1, 2, 1, 1, 1])
private def n2165 : MainTree := .split 5 0 n2166 n2169
private def n2157 : MainTree := .split 4 0 n2158 n2165
private def n2149 : MainTree := .split 2 0 n2150 n2157
private def n2174 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 2, 0, 0, 0])
private def n2175 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 2, 0, 0, 1])
private def n2173 : MainTree := .split 6 0 n2174 n2175
private def n2177 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 2, 0, 1, 0])
private def n2178 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 2, 0, 1, 1])
private def n2176 : MainTree := .split 6 0 n2177 n2178
private def n2172 : MainTree := .split 5 0 n2173 n2176
private def n2181 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 2, 1, 0, 0])
private def n2182 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 2, 1, 0, 1])
private def n2180 : MainTree := .split 6 0 n2181 n2182
private def n2184 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 2, 1, 1, 0])
private def n2185 : MainTree := .leaf (mainGapLeaf ![17, 1, 0, 2, 1, 1, 1])
private def n2183 : MainTree := .split 6 0 n2184 n2185
private def n2179 : MainTree := .split 5 0 n2180 n2183
private def n2171 : MainTree := .split 4 0 n2172 n2179
private def n2189 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 2, 0, 0, 0])
private def n2190 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 2, 0, 0, 1])
private def n2188 : MainTree := .split 6 0 n2189 n2190
private def n2192 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 2, 0, 1, 0])
private def n2193 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 2, 0, 1, 1])
private def n2191 : MainTree := .split 6 0 n2192 n2193
private def n2187 : MainTree := .split 5 0 n2188 n2191
private def n2196 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 2, 1, 0, 0])
private def n2197 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 2, 1, 0, 1])
private def n2195 : MainTree := .split 6 0 n2196 n2197
private def n2199 : MainTree := .leaf (mainGapLeaf ![17, 1, 1, 2, 1, 1, 0])
private def d2200 : List ℕ := [
    0x3603104c138064080308343c02a0640622a01901c0d8002600240680043c002078240020480181800c030000,
    0x1c04847a07a5405a0049880f8140910910e0840051240323e0cc092018200608940349008412803830818810,
    0xcc5001d1812a8369800490507203483c3d000c6e0b03043c46804a4e0014351840f2560261f81e41b020006,
    0x286d09d360152221140c9138089240632780d8881e22a24c0550245a0194650393c8364dc0ac4b0548660a0,
    0x1866704b170022908d8990214211980c50b04a80f0994884e50c033218ae0091b2258084800c606a6804d1e1,
    0xa46653c0932d80358c072424630409600a84984aa000363e920874428669e010901c3a14412903a3f0412a8,
    0x3f5080b486e290ba0211890fa570713080a248cfe0f63a01c5512110887c0b500b1c8e40928b83141f87caa4,
    0x30a460f50de2b2c10268b23f20b16c0f33981b5bc0d20829c8f60071c27005a1861ea9803d95a54235027274,
    0x5a80a52d4803923381e9a8690288f48dd378509b40b1306970ab2301a2c0825a711480a9281ca0d6511f803e,
    0x2f09289f1b96c82b489259118ce0a9a2c19af6099026142b49260672828801d9143cc555600db374c049a0ae,
    0x25c275040237504092493d4380dcd13c822278d5e01636ca4098b6215609568904114ac1150cb3491404f1e5,
    0x1d8e60d9a8c25b0e0c9086202cc9560c70b46854009b2e8055231b56404ed0d3613284399a0895753811485c,
    0x8505c521b1c0ec8597819178442c42b312c83a9880595144ad024b003e3f9229d85546790cbc421a5c95c813,
    0x402b807d9d40eaa990ab803369e9e09f42dc03dca0e9635501448bc31c3f5340838105895485633a9f04ba02,
    0x5d462d325100fe57952a3861414cff2798485b4e93190e6531fc2135d8118c6c983e4398b0b92618154938ba,
    0x5d210c8e1ee2bab2071c68384c245b1fd5b83dd314883a2a8dbe0d608a9d9a81f18445ac72b91388529b80b9,
    0x698298f6cf84a4518e0bf26d82d4c391a4c2d00ada341aac1827a757c07ec172da842950e706f7e8525bd5a0,
    0x760946411cb28afc51203f354f408cb4a3d6b12b80df37cc154c36a1660b52f2d9908735193791a66b22c273,
    0x6752055a22e19f150d4bdac00d245197c49c6f594143990889b49164bacf0abac29d08c581bdc26c2956b02b,
    0x9c88b5493d92668325c0275a6eb08324dab0ac8d32218a4f308a9e72f4b05d01bb5284d5b30af5ab1012d88e,
    0x522d8e1e19620acd845c105633891585e34b1454209f4150c0bcbaa496c92e813f43cd957c3ca2262355f339,
    0x21ecd6502bb1dce6a70b140baa3897cb44130eb303a92067715721d71068e942827925d95e8177386dd91548,
    0x2e63b58f399a88a35794393269b28c087667030b32adb70c482da065032ca1617548e76990c00436bd0cabc6,
    0x7f885dc15a85e2f0e4e1f62cae5875c70623509458be40b2c5720ff4d5240ecc0a556e131819f4fcf15ac42a,
    0x4f6d50fac262dee568031b29cfeaa0b7417abb8c7d144d326a04963478c382ba7d7d080ec42e28527598e877,
    0x84aee2451d329adf9fcda45da11da94993e6b32bc0e77271b0e330dc30dc85da665c344a461d554e8e9c0c60,
    0x46cdf46bc5c4eef8b043518473f12b1c57ec52e68371b44bac8f265a22d10afaca9e08e63530b7c9a40ffade,
    0x7c330017adb768956431cf7eb581bd9ae8b5685ea11d69c7beba2c99f51a4e1a9c6dc2dd6ec484c77a1a1489,
    0x4becfa42c189d48ccd6bde8b3811a68a77653e529b2cbb051df9ccc44cdb73c3d2236b19a0d729d88d583a9a,
    0xc90e8a74a967ba4de5e2d78859a1d8c83ab8ad912c563574c1e8e026965f962d717486fd95550533329b5c44,
    0x52ad9d7d441a4023d9dc1456b39917c55b80f6d074bac030d0bebae49f75194d5a99288d7e3ce22ecf6542c3,
    0x5f34a9e5ca457ee7a72c78a94a4d06c3e973991d690782556559b8cc7069e29d2c50cf361917b64ce86e954c,
    0x2eee7684323d5100aa4af687a65e8e33794504671dbc62c17d42cb641764218e6275677992dd180887dc55b0,
    0x70d007195ac5eaf1dad4a1b003bdcdc7462b51947cb5c410ed3751acc3250eec0e55f8d1c4dbaa52a0dae42e,
    0xc631913fbeac20d66c542ba08c7dff5459b16a979a6d93d466069678e56e589becd3081e59d8c5cd0b6491db,
    0xd28fa70d5895c6ef2471d77fb5a1c1c62b52d5a4e9f7af8e5e81471a87871bb0bf5cb45935df092302d1f385,
    0x89899e89dec68d2367923b7cd1874960c6ab09ddd501bc053dfdcd46eb69977d15d0126d6757a9e88f63730f,
    0x23ed16bb2cbca13c635a9e7cba46622df8959c1dcdea917591bfc5eb4b4e30535359b3fabcc6d38f34b0cb73,
    0xc0cd3ebacfb65d76aaa29d99cdbe24e7abd2d0e0e4ee46f176e43e3985825db4fd4af771fbd629a368f3e3d6,
    0xc0b663353b365b57aecccd44f4cb3cbd3958b1eb9e4c74d3b6a929b88d307363b590f06ab0e4035f16e9a3d5,
    0x97b8a221d22cd305aaeab7c7915ee1531c070d8bfba5baccaf58551996bfa22d2467f2aa0ce4a9d7711efcbe,
    0xd5901aa6db25f729a90c159cf1eae0ea041f2eeca435cccebeead5b71d8eada2fda5cf3e54e497471f2a7297,
    0xcc7258efc05c6ce2ed8d2b6bd296c239fa151e75554bc490fe8f665bf104dc6dbec734b543d9286743193dd3,
    0x9b588537d1bbe925607e35b76fbb4d6146bb63a17d09d5300e6e5ae5ef477444a3b051dadeb17d392df11591,
    0xc2362ddf505bc8ffeb54d9b57a124fd7ecb11cdf6e1ed3363573df29275b1c3e338cd6b70935ba0d6063ad47,
    0xd02b3ebde549eb1bf4ae1b89d9d1dedee91f5a631d3cc1cd5ebed03bc535b0eb77a2fa0af8cf647f1974b3eb,
    0x8979c6f5c1eacb9122fdcaa7382e7fdded7134e26e7ebdad1f294f3b98f9f49cc6c1b9c9ddd66bc3356d3d3a,
    0x83771b20d35c0f66997ddbd6955667e7b95d077274efb9330ece66e76f776b1e42a6d9f5ebd77ca35594fcc5,
    0x82f8f6e1ea2b2d0deebeb1b6cbfe92cabc971fae2ea497f8aacce6babf8fa99cadc9ae9f59553c5911e9366d,
    0x9bd8968fe8abf36ff4f593a1bab603db3d1929ec347bc4da86cae67bf4e3f1ddb5a5f43a3eeaea9f8a691dfc,
    0xc3f7ceb6c67c2741ef34dbd0d7d72d3efd37856c7d6e9bb6bf44d83cb91df4ee23bed25f1be166bf61685eab,
    0xd739ff29dcd98f9ceb3e46a779575d44fceb7bee753dc1f78f5e4d7d0795a7be97cecefef2d6ba7da16bfe59,
    0xd5fa3afeea3b2f6de3fea5c577fb1feb3c5b49ee3ea6b37ad657e4fc5d67737e43a6fadaabc1fc8b72ecf5df,
    0xd7f97f47dffd4f8bf5bd9fc8faeee7ebdcaf9de9febebcfa1f2dd6fcbb7df0bcdfd1797b4fe8db0f89efdd0f]
private def a2200 : List ℕ :=
  certificateIndexedDivisors (exponentFactors boxPrimes ![17, 1, 1, 2, 1, 1, 1])
    2048 32 1728 d2200
private def n2200 : MainTree := .leaf (mainGapLeafOfDivisors ![17, 1, 1, 2, 1, 1, 1] a2200)
private def n2198 : MainTree := .split 6 0 n2199 n2200
private def n2194 : MainTree := .split 5 0 n2195 n2198
private def n2186 : MainTree := .split 4 0 n2187 n2194
private def n2170 : MainTree := .split 2 0 n2171 n2186
private def n2148 : MainTree := .split 1 0 n2149 n2170
private def n2104 : MainTree := .split 3 0 n2105 n2148
private def n1802 : MainTree := .split 0 8 n1803 n2104

private theorem c1805 : C ![4, 0, 0, 0, 0, 0, 0] ![8, 0, 1, 0, 1, 1, 1] n1805 := by
  decide +kernel

private theorem c1837 : C ![4, 1, 0, 0, 0, 0, 0] ![8, 1, 0, 0, 1, 1, 1] n1837 := by
  decide +kernel

private theorem c1868 : C ![4, 1, 1, 0, 0, 0, 0] ![8, 1, 1, 0, 1, 1, 1] n1868 := by
  decide +kernel

private theorem c1836 : C ![4, 1, 0, 0, 0, 0, 0] ![8, 1, 1, 0, 1, 1, 1] n1836 := by
  exact checkExponentBoxTree_join c1837 c1868 (by decide +kernel)

private theorem c1804 : C ![4, 0, 0, 0, 0, 0, 0] ![8, 1, 1, 0, 1, 1, 1] n1804 := by
  exact checkExponentBoxTree_join c1805 c1836 (by decide +kernel)

private theorem c1915 : C ![4, 0, 0, 1, 0, 0, 0] ![8, 0, 0, 2, 1, 1, 1] n1915 := by
  decide +kernel

private theorem c1935 : C ![4, 0, 1, 1, 0, 0, 0] ![8, 0, 1, 2, 0, 1, 1] n1935 := by
  decide +kernel

private theorem c1950 : C ![4, 0, 1, 1, 1, 0, 0] ![8, 0, 1, 2, 1, 1, 1] n1950 := by
  decide +kernel

private theorem c1934 : C ![4, 0, 1, 1, 0, 0, 0] ![8, 0, 1, 2, 1, 1, 1] n1934 := by
  exact checkExponentBoxTree_join c1935 c1950 (by decide +kernel)

private theorem c1914 : C ![4, 0, 0, 1, 0, 0, 0] ![8, 0, 1, 2, 1, 1, 1] n1914 := by
  exact checkExponentBoxTree_join c1915 c1934 (by decide +kernel)

private theorem c1965 : C ![4, 1, 0, 1, 0, 0, 0] ![8, 1, 0, 2, 0, 1, 1] n1965 := by
  decide +kernel

private theorem c1998 : C ![4, 1, 0, 1, 1, 0, 0] ![8, 1, 0, 2, 1, 1, 1] n1998 := by
  decide +kernel

private theorem c1964 : C ![4, 1, 0, 1, 0, 0, 0] ![8, 1, 0, 2, 1, 1, 1] n1964 := by
  exact checkExponentBoxTree_join c1965 c1998 (by decide +kernel)

private theorem c2025 : C ![4, 1, 1, 1, 0, 0, 0] ![8, 1, 1, 2, 0, 0, 1] n2025 := by
  decide +kernel

private theorem c2049 : C ![4, 1, 1, 1, 0, 1, 0] ![8, 1, 1, 2, 0, 1, 0] n2049 := by
  decide +kernel

private theorem c2060 : C ![4, 1, 1, 1, 0, 1, 1] ![8, 1, 1, 2, 0, 1, 1] n2060 := by
  decide +kernel

private theorem c2048 : C ![4, 1, 1, 1, 0, 1, 0] ![8, 1, 1, 2, 0, 1, 1] n2048 := by
  exact checkExponentBoxTree_join c2049 c2060 (by decide +kernel)

private theorem c2024 : C ![4, 1, 1, 1, 0, 0, 0] ![8, 1, 1, 2, 0, 1, 1] n2024 := by
  exact checkExponentBoxTree_join c2025 c2048 (by decide +kernel)

private theorem c2069 : C ![4, 1, 1, 1, 1, 0, 0] ![8, 1, 1, 2, 1, 0, 0] n2069 := by
  decide +kernel

private theorem c2080 : C ![4, 1, 1, 1, 1, 0, 1] ![8, 1, 1, 2, 1, 0, 1] n2080 := by
  decide +kernel

private theorem c2068 : C ![4, 1, 1, 1, 1, 0, 0] ![8, 1, 1, 2, 1, 0, 1] n2068 := by
  exact checkExponentBoxTree_join c2069 c2080 (by decide +kernel)

private theorem c2090 : C ![4, 1, 1, 1, 1, 1, 0] ![8, 1, 1, 2, 1, 1, 0] n2090 := by
  decide +kernel

private theorem c2100 : C ![4, 1, 1, 1, 1, 1, 1] ![5, 1, 1, 2, 1, 1, 1] n2100 := by
  decide +kernel

private theorem c2103 : C ![6, 1, 1, 1, 1, 1, 1] ![8, 1, 1, 2, 1, 1, 1] n2103 := by
  decide +kernel

private theorem c2099 : C ![4, 1, 1, 1, 1, 1, 1] ![8, 1, 1, 2, 1, 1, 1] n2099 := by
  exact checkExponentBoxTree_join c2100 c2103 (by decide +kernel)

private theorem c2089 : C ![4, 1, 1, 1, 1, 1, 0] ![8, 1, 1, 2, 1, 1, 1] n2089 := by
  exact checkExponentBoxTree_join c2090 c2099 (by decide +kernel)

private theorem c2067 : C ![4, 1, 1, 1, 1, 0, 0] ![8, 1, 1, 2, 1, 1, 1] n2067 := by
  exact checkExponentBoxTree_join c2068 c2089 (by decide +kernel)

private theorem c2023 : C ![4, 1, 1, 1, 0, 0, 0] ![8, 1, 1, 2, 1, 1, 1] n2023 := by
  exact checkExponentBoxTree_join c2024 c2067 (by decide +kernel)

private theorem c1963 : C ![4, 1, 0, 1, 0, 0, 0] ![8, 1, 1, 2, 1, 1, 1] n1963 := by
  exact checkExponentBoxTree_join c1964 c2023 (by decide +kernel)

private theorem c1913 : C ![4, 0, 0, 1, 0, 0, 0] ![8, 1, 1, 2, 1, 1, 1] n1913 := by
  exact checkExponentBoxTree_join c1914 c1963 (by decide +kernel)

private theorem c1803 : C ![4, 0, 0, 0, 0, 0, 0] ![8, 1, 1, 2, 1, 1, 1] n1803 := by
  exact checkExponentBoxTree_join c1804 c1913 (by decide +kernel)

private theorem c2106 : C ![9, 0, 0, 0, 0, 0, 0] ![17, 0, 1, 0, 1, 1, 1] n2106 := by
  decide +kernel

private theorem c2122 : C ![9, 1, 0, 0, 0, 0, 0] ![17, 1, 0, 0, 1, 1, 1] n2122 := by
  decide +kernel

private theorem c2134 : C ![9, 1, 1, 0, 0, 0, 0] ![17, 1, 1, 0, 0, 1, 1] n2134 := by
  decide +kernel

private theorem c2141 : C ![9, 1, 1, 0, 1, 0, 0] ![17, 1, 1, 0, 1, 1, 1] n2141 := by
  decide +kernel

private theorem c2133 : C ![9, 1, 1, 0, 0, 0, 0] ![17, 1, 1, 0, 1, 1, 1] n2133 := by
  exact checkExponentBoxTree_join c2134 c2141 (by decide +kernel)

private theorem c2121 : C ![9, 1, 0, 0, 0, 0, 0] ![17, 1, 1, 0, 1, 1, 1] n2121 := by
  exact checkExponentBoxTree_join c2122 c2133 (by decide +kernel)

private theorem c2105 : C ![9, 0, 0, 0, 0, 0, 0] ![17, 1, 1, 0, 1, 1, 1] n2105 := by
  exact checkExponentBoxTree_join c2106 c2121 (by decide +kernel)

private theorem c2150 : C ![9, 0, 0, 1, 0, 0, 0] ![17, 0, 0, 2, 1, 1, 1] n2150 := by
  decide +kernel

private theorem c2158 : C ![9, 0, 1, 1, 0, 0, 0] ![17, 0, 1, 2, 0, 1, 1] n2158 := by
  decide +kernel

private theorem c2165 : C ![9, 0, 1, 1, 1, 0, 0] ![17, 0, 1, 2, 1, 1, 1] n2165 := by
  decide +kernel

private theorem c2157 : C ![9, 0, 1, 1, 0, 0, 0] ![17, 0, 1, 2, 1, 1, 1] n2157 := by
  exact checkExponentBoxTree_join c2158 c2165 (by decide +kernel)

private theorem c2149 : C ![9, 0, 0, 1, 0, 0, 0] ![17, 0, 1, 2, 1, 1, 1] n2149 := by
  exact checkExponentBoxTree_join c2150 c2157 (by decide +kernel)

private theorem c2172 : C ![9, 1, 0, 1, 0, 0, 0] ![17, 1, 0, 2, 0, 1, 1] n2172 := by
  decide +kernel

private theorem c2180 : C ![9, 1, 0, 1, 1, 0, 0] ![17, 1, 0, 2, 1, 0, 1] n2180 := by
  decide +kernel

private theorem c2183 : C ![9, 1, 0, 1, 1, 1, 0] ![17, 1, 0, 2, 1, 1, 1] n2183 := by
  decide +kernel

private theorem c2179 : C ![9, 1, 0, 1, 1, 0, 0] ![17, 1, 0, 2, 1, 1, 1] n2179 := by
  exact checkExponentBoxTree_join c2180 c2183 (by decide +kernel)

private theorem c2171 : C ![9, 1, 0, 1, 0, 0, 0] ![17, 1, 0, 2, 1, 1, 1] n2171 := by
  exact checkExponentBoxTree_join c2172 c2179 (by decide +kernel)

private theorem c2188 : C ![9, 1, 1, 1, 0, 0, 0] ![17, 1, 1, 2, 0, 0, 1] n2188 := by
  decide +kernel

private theorem c2191 : C ![9, 1, 1, 1, 0, 1, 0] ![17, 1, 1, 2, 0, 1, 1] n2191 := by
  decide +kernel

private theorem c2187 : C ![9, 1, 1, 1, 0, 0, 0] ![17, 1, 1, 2, 0, 1, 1] n2187 := by
  exact checkExponentBoxTree_join c2188 c2191 (by decide +kernel)

private theorem c2195 : C ![9, 1, 1, 1, 1, 0, 0] ![17, 1, 1, 2, 1, 0, 1] n2195 := by
  decide +kernel

private theorem c2199 : C ![9, 1, 1, 1, 1, 1, 0] ![17, 1, 1, 2, 1, 1, 0] n2199 := by
  decide +kernel

private theorem c2200 : C ![9, 1, 1, 1, 1, 1, 1] ![17, 1, 1, 2, 1, 1, 1] n2200 := by
  decide +kernel

private theorem c2198 : C ![9, 1, 1, 1, 1, 1, 0] ![17, 1, 1, 2, 1, 1, 1] n2198 := by
  exact checkExponentBoxTree_join c2199 c2200 (by decide +kernel)

private theorem c2194 : C ![9, 1, 1, 1, 1, 0, 0] ![17, 1, 1, 2, 1, 1, 1] n2194 := by
  exact checkExponentBoxTree_join c2195 c2198 (by decide +kernel)

private theorem c2186 : C ![9, 1, 1, 1, 0, 0, 0] ![17, 1, 1, 2, 1, 1, 1] n2186 := by
  exact checkExponentBoxTree_join c2187 c2194 (by decide +kernel)

private theorem c2170 : C ![9, 1, 0, 1, 0, 0, 0] ![17, 1, 1, 2, 1, 1, 1] n2170 := by
  exact checkExponentBoxTree_join c2171 c2186 (by decide +kernel)

private theorem c2148 : C ![9, 0, 0, 1, 0, 0, 0] ![17, 1, 1, 2, 1, 1, 1] n2148 := by
  exact checkExponentBoxTree_join c2149 c2170 (by decide +kernel)

private theorem c2104 : C ![9, 0, 0, 0, 0, 0, 0] ![17, 1, 1, 2, 1, 1, 1] n2104 := by
  exact checkExponentBoxTree_join c2105 c2148 (by decide +kernel)

private theorem c1802 : C ![4, 0, 0, 0, 0, 0, 0] ![17, 1, 1, 2, 1, 1, 1] n1802 := by
  exact checkExponentBoxTree_join c1803 c2104 (by decide +kernel)

/-- The complete binary certificate at this subtree root. -/
def certificate : MainTree := n1802

theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes lo hi certificate = true := c1802

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.Main04
