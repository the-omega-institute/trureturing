/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table250
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table250.pv1997813
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table034
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table051
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table065
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table066
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table137

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1997813 : Nat.Prime 1997813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv97,pv271]) (by decide +kernel)
def pv1997813 : PrimeValue := ⟨1997813, pr1997813⟩
private theorem pr1997843 : Nat.Prime 1997843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv12973]) (by decide +kernel)
def pv1997843 : PrimeValue := ⟨1997843, pr1997843⟩
private theorem pr1997921 : Nat.Prime 1997921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv12487]) (by decide +kernel)
def pv1997921 : PrimeValue := ⟨1997921, pr1997921⟩
private theorem pr1998233 : Nat.Prime 1998233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv249779]) (by decide +kernel)
def pv1998233 : PrimeValue := ⟨1998233, pr1998233⟩
private theorem pr1998371 : Nat.Prime 1998371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv37,pv491]) (by decide +kernel)
def pv1998371 : PrimeValue := ⟨1998371, pr1998371⟩
private theorem pr1998413 : Nat.Prime 1998413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv38431]) (by decide +kernel)
def pv1998413 : PrimeValue := ⟨1998413, pr1998413⟩
private theorem pr1998701 : Nat.Prime 1998701 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv23,pv79]) (by decide +kernel)
def pv1998701 : PrimeValue := ⟨1998701, pr1998701⟩
private theorem pr1999499 : Nat.Prime 1999499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv999749]) (by decide +kernel)
def pv1999499 : PrimeValue := ⟨1999499, pr1999499⟩
private theorem pr1999619 : Nat.Prime 1999619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv999809]) (by decide +kernel)
def pv1999619 : PrimeValue := ⟨1999619, pr1999619⟩
private theorem pr1999661 : Nat.Prime 1999661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv7691]) (by decide +kernel)
def pv1999661 : PrimeValue := ⟨1999661, pr1999661⟩
private theorem pr1999691 : Nat.Prime 1999691 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv53]) (by decide +kernel)
def pv1999691 : PrimeValue := ⟨1999691, pr1999691⟩
private theorem pr1999733 : Nat.Prime 1999733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv71419]) (by decide +kernel)
def pv1999733 : PrimeValue := ⟨1999733, pr1999733⟩
private theorem pr1999799 : Nat.Prime 1999799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv307,pv3257]) (by decide +kernel)
def pv1999799 : PrimeValue := ⟨1999799, pr1999799⟩
private theorem pr1999853 : Nat.Prime 1999853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv263,pv1901]) (by decide +kernel)
def pv1999853 : PrimeValue := ⟨1999853, pr1999853⟩
private theorem pr1999859 : Nat.Prime 1999859 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv211,pv677]) (by decide +kernel)
def pv1999859 : PrimeValue := ⟨1999859, pr1999859⟩
private theorem pr2000039 : Nat.Prime 2000039 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv47,pv21277]) (by decide +kernel)
def pv2000039 : PrimeValue := ⟨2000039, pr2000039⟩
private theorem pr2000261 : Nat.Prime 2000261 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv103,pv971]) (by decide +kernel)
def pv2000261 : PrimeValue := ⟨2000261, pr2000261⟩
private theorem pr2000573 : Nat.Prime 2000573 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv59,pv173]) (by decide +kernel)
def pv2000573 : PrimeValue := ⟨2000573, pr2000573⟩
private theorem pr2000699 : Nat.Prime 2000699 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv142907]) (by decide +kernel)
def pv2000699 : PrimeValue := ⟨2000699, pr2000699⟩
private theorem pr2000903 : Nat.Prime 2000903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv563,pv1777]) (by decide +kernel)
def pv2000903 : PrimeValue := ⟨2000903, pr2000903⟩
private theorem pr2000969 : Nat.Prime 2000969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv14713]) (by decide +kernel)
def pv2000969 : PrimeValue := ⟨2000969, pr2000969⟩
private theorem pr2001281 : Nat.Prime 2001281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv53,pv59]) (by decide +kernel)
def pv2001281 : PrimeValue := ⟨2001281, pr2001281⟩
private theorem pr2001371 : Nat.Prime 2001371 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv28591]) (by decide +kernel)
def pv2001371 : PrimeValue := ⟨2001371, pr2001371⟩
private theorem pr2001509 : Nat.Prime 2001509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv661,pv757]) (by decide +kernel)
def pv2001509 : PrimeValue := ⟨2001509, pr2001509⟩
private theorem pr2001539 : Nat.Prime 2001539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv41,pv317]) (by decide +kernel)
def pv2001539 : PrimeValue := ⟨2001539, pr2001539⟩
private theorem pr2001833 : Nat.Prime 2001833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv35747]) (by decide +kernel)
def pv2001833 : PrimeValue := ⟨2001833, pr2001833⟩
private theorem pr2002289 : Nat.Prime 2002289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv5441]) (by decide +kernel)
def pv2002289 : PrimeValue := ⟨2002289, pr2002289⟩
private theorem pr2002349 : Nat.Prime 2002349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv500587]) (by decide +kernel)
def pv2002349 : PrimeValue := ⟨2002349, pr2002349⟩
private theorem pr2002673 : Nat.Prime 2002673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17881]) (by decide +kernel)
def pv2002673 : PrimeValue := ⟨2002673, pr2002673⟩
private theorem pr2002883 : Nat.Prime 2002883 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv143063]) (by decide +kernel)
def pv2002883 : PrimeValue := ⟨2002883, pr2002883⟩
private theorem pr2002919 : Nat.Prime 2002919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv1001459]) (by decide +kernel)
def pv2002919 : PrimeValue := ⟨2002919, pr2002919⟩
private theorem pr2003009 : Nat.Prime 2003009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv263]) (by decide +kernel)
def pv2003009 : PrimeValue := ⟨2003009, pr2003009⟩
private theorem pr2003051 : Nat.Prime 2003051 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv59,pv97]) (by decide +kernel)
def pv2003051 : PrimeValue := ⟨2003051, pr2003051⟩
private theorem pr2003153 : Nat.Prime 2003153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv125197]) (by decide +kernel)
def pv2003153 : PrimeValue := ⟨2003153, pr2003153⟩
private theorem pr2003159 : Nat.Prime 2003159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv31,pv32309]) (by decide +kernel)
def pv2003159 : PrimeValue := ⟨2003159, pr2003159⟩
private theorem pr2003201 : Nat.Prime 2003201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv313]) (by decide +kernel)
def pv2003201 : PrimeValue := ⟨2003201, pr2003201⟩
private theorem pr2003273 : Nat.Prime 2003273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv250409]) (by decide +kernel)
def pv2003273 : PrimeValue := ⟨2003273, pr2003273⟩
private theorem pr2003381 : Nat.Prime 2003381 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv100169]) (by decide +kernel)
def pv2003381 : PrimeValue := ⟨2003381, pr2003381⟩
private theorem pr2003411 : Nat.Prime 2003411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv200341]) (by decide +kernel)
def pv2003411 : PrimeValue := ⟨2003411, pr2003411⟩
private theorem pr2003591 : Nat.Prime 2003591 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv191,pv1049]) (by decide +kernel)
def pv2003591 : PrimeValue := ⟨2003591, pr2003591⟩
private theorem pr2003681 : Nat.Prime 2003681 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv7,pv1789]) (by decide +kernel)
def pv2003681 : PrimeValue := ⟨2003681, pr2003681⟩
private theorem pr2003723 : Nat.Prime 2003723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv8419]) (by decide +kernel)
def pv2003723 : PrimeValue := ⟨2003723, pr2003723⟩
private theorem pr2003741 : Nat.Prime 2003741 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv5273]) (by decide +kernel)
def pv2003741 : PrimeValue := ⟨2003741, pr2003741⟩
private theorem pr2003861 : Nat.Prime 2003861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv100193]) (by decide +kernel)
def pv2003861 : PrimeValue := ⟨2003861, pr2003861⟩
private theorem pr2003999 : Nat.Prime 2003999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv41,pv24439]) (by decide +kernel)
def pv2003999 : PrimeValue := ⟨2003999, pr2003999⟩
private theorem pr2004773 : Nat.Prime 2004773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv23,pv283]) (by decide +kernel)
def pv2004773 : PrimeValue := ⟨2004773, pr2004773⟩
private theorem pr2004809 : Nat.Prime 2004809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv37,pv521]) (by decide +kernel)
def pv2004809 : PrimeValue := ⟨2004809, pr2004809⟩
private theorem pr2004833 : Nat.Prime 2004833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv43,pv47]) (by decide +kernel)
def pv2004833 : PrimeValue := ⟨2004833, pr2004833⟩
private theorem pr2004839 : Nat.Prime 2004839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv91129]) (by decide +kernel)
def pv2004839 : PrimeValue := ⟨2004839, pr2004839⟩
private theorem pr2004911 : Nat.Prime 2004911 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv23,pv379]) (by decide +kernel)
def pv2004911 : PrimeValue := ⟨2004911, pr2004911⟩
private theorem pr2005319 : Nat.Prime 2005319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv227,pv631]) (by decide +kernel)
def pv2005319 : PrimeValue := ⟨2005319, pr2005319⟩
private theorem pr2005331 : Nat.Prime 2005331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv127,pv1579]) (by decide +kernel)
def pv2005331 : PrimeValue := ⟨2005331, pr2005331⟩
private theorem pr2005673 : Nat.Prime 2005673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv250709]) (by decide +kernel)
def pv2005673 : PrimeValue := ⟨2005673, pr2005673⟩
private theorem pr2005739 : Nat.Prime 2005739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv6229]) (by decide +kernel)
def pv2005739 : PrimeValue := ⟨2005739, pr2005739⟩
private theorem pr2005859 : Nat.Prime 2005859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1002929]) (by decide +kernel)
def pv2005859 : PrimeValue := ⟨2005859, pr2005859⟩
private theorem pr2005931 : Nat.Prime 2005931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv6917]) (by decide +kernel)
def pv2005931 : PrimeValue := ⟨2005931, pr2005931⟩
private theorem pr2006033 : Nat.Prime 2006033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17911]) (by decide +kernel)
def pv2006033 : PrimeValue := ⟨2006033, pr2006033⟩
private theorem pr2006183 : Nat.Prime 2006183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv1003091]) (by decide +kernel)
def pv2006183 : PrimeValue := ⟨2006183, pr2006183⟩
private theorem pr2006579 : Nat.Prime 2006579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv8431]) (by decide +kernel)
def pv2006579 : PrimeValue := ⟨2006579, pr2006579⟩
private theorem pr2006783 : Nat.Prime 2006783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv59023]) (by decide +kernel)
def pv2006783 : PrimeValue := ⟨2006783, pr2006783⟩
private theorem pr2006891 : Nat.Prime 2006891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv200689]) (by decide +kernel)
def pv2006891 : PrimeValue := ⟨2006891, pr2006891⟩
private theorem pr2007251 : Nat.Prime 2007251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv31,pv37]) (by decide +kernel)
def pv2007251 : PrimeValue := ⟨2007251, pr2007251⟩
private theorem pr2007431 : Nat.Prime 2007431 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv197,pv1019]) (by decide +kernel)
def pv2007431 : PrimeValue := ⟨2007431, pr2007431⟩
private theorem pr2007899 : Nat.Prime 2007899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv593,pv1693]) (by decide +kernel)
def pv2007899 : PrimeValue := ⟨2007899, pr2007899⟩
private theorem pr2008421 : Nat.Prime 2008421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv137,pv733]) (by decide +kernel)
def pv2008421 : PrimeValue := ⟨2008421, pr2008421⟩
private theorem pr2008481 : Nat.Prime 2008481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv12553]) (by decide +kernel)
def pv2008481 : PrimeValue := ⟨2008481, pr2008481⟩
private theorem pr2008553 : Nat.Prime 2008553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv31,pv89]) (by decide +kernel)
def pv2008553 : PrimeValue := ⟨2008553, pr2008553⟩
private theorem pr2008679 : Nat.Prime 2008679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv143477]) (by decide +kernel)
def pv2008679 : PrimeValue := ⟨2008679, pr2008679⟩
private theorem pr2008763 : Nat.Prime 2008763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv143483]) (by decide +kernel)
def pv2008763 : PrimeValue := ⟨2008763, pr2008763⟩
private theorem pr2008823 : Nat.Prime 2008823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv59083]) (by decide +kernel)
def pv2008823 : PrimeValue := ⟨2008823, pr2008823⟩
private theorem pr2008901 : Nat.Prime 2008901 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv20089]) (by decide +kernel)
def pv2008901 : PrimeValue := ⟨2008901, pr2008901⟩
private theorem pr2009321 : Nat.Prime 2009321 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv191,pv263]) (by decide +kernel)
def pv2009321 : PrimeValue := ⟨2009321, pr2009321⟩
private theorem pr2009489 : Nat.Prime 2009489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv9661]) (by decide +kernel)
def pv2009489 : PrimeValue := ⟨2009489, pr2009489⟩
private theorem pr2009603 : Nat.Prime 2009603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv79]) (by decide +kernel)
def pv2009603 : PrimeValue := ⟨2009603, pr2009603⟩
private theorem pr2009783 : Nat.Prime 2009783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv52889]) (by decide +kernel)
def pv2009783 : PrimeValue := ⟨2009783, pr2009783⟩
private theorem pr2009789 : Nat.Prime 2009789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv45677]) (by decide +kernel)
def pv2009789 : PrimeValue := ⟨2009789, pr2009789⟩
private theorem pr2009831 : Nat.Prime 2009831 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv200983]) (by decide +kernel)
def pv2009831 : PrimeValue := ⟨2009831, pr2009831⟩
private theorem pr2009921 : Nat.Prime 2009921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv571]) (by decide +kernel)
def pv2009921 : PrimeValue := ⟨2009921, pr2009921⟩
private theorem pr2010083 : Nat.Prime 2010083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1005041]) (by decide +kernel)
def pv2010083 : PrimeValue := ⟨2010083, pr2010083⟩
private theorem pr2010161 : Nat.Prime 2010161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv25127]) (by decide +kernel)
def pv2010161 : PrimeValue := ⟨2010161, pr2010161⟩
private theorem pr2010311 : Nat.Prime 2010311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv201031]) (by decide +kernel)
def pv2010311 : PrimeValue := ⟨2010311, pr2010311⟩
private theorem pr2010689 : Nat.Prime 2010689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv89,pv353]) (by decide +kernel)
def pv2010689 : PrimeValue := ⟨2010689, pr2010689⟩
private theorem pr2011073 : Nat.Prime 2011073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv67]) (by decide +kernel)
def pv2011073 : PrimeValue := ⟨2011073, pr2011073⟩
private theorem pr2011241 : Nat.Prime 2011241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv653]) (by decide +kernel)
def pv2011241 : PrimeValue := ⟨2011241, pr2011241⟩
private theorem pr2011391 : Nat.Prime 2011391 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv201139]) (by decide +kernel)
def pv2011391 : PrimeValue := ⟨2011391, pr2011391⟩
private theorem pr2011631 : Nat.Prime 2011631 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv201163]) (by decide +kernel)
def pv2011631 : PrimeValue := ⟨2011631, pr2011631⟩
private theorem pr2011673 : Nat.Prime 2011673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv23,pv29]) (by decide +kernel)
def pv2011673 : PrimeValue := ⟨2011673, pr2011673⟩
private theorem pr2011799 : Nat.Prime 2011799 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv43,pv149,pv157]) (by decide +kernel)
def pv2011799 : PrimeValue := ⟨2011799, pr2011799⟩
private theorem pr2011973 : Nat.Prime 2011973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv6367]) (by decide +kernel)
def pv2011973 : PrimeValue := ⟨2011973, pr2011973⟩
private theorem pr2012243 : Nat.Prime 2012243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv9403]) (by decide +kernel)
def pv2012243 : PrimeValue := ⟨2012243, pr2012243⟩
private theorem pr2012333 : Nat.Prime 2012333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv10267]) (by decide +kernel)
def pv2012333 : PrimeValue := ⟨2012333, pr2012333⟩
private theorem pr2012639 : Nat.Prime 2012639 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv23,pv43753]) (by decide +kernel)
def pv2012639 : PrimeValue := ⟨2012639, pr2012639⟩
private theorem pr2012663 : Nat.Prime 2012663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv1006331]) (by decide +kernel)
def pv2012663 : PrimeValue := ⟨2012663, pr2012663⟩
private theorem pr2012693 : Nat.Prime 2012693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv149,pv307]) (by decide +kernel)
def pv2012693 : PrimeValue := ⟨2012693, pr2012693⟩
private theorem pr2012849 : Nat.Prime 2012849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv125803]) (by decide +kernel)
def pv2012849 : PrimeValue := ⟨2012849, pr2012849⟩
private theorem pr2013113 : Nat.Prime 2013113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv251639]) (by decide +kernel)
def pv2013113 : PrimeValue := ⟨2013113, pr2013113⟩
private theorem pr2013359 : Nat.Prime 2013359 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv89,pv11311]) (by decide +kernel)
def pv2013359 : PrimeValue := ⟨2013359, pr2013359⟩
private theorem pr2013593 : Nat.Prime 2013593 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv41,pv877]) (by decide +kernel)
def pv2013593 : PrimeValue := ⟨2013593, pr2013593⟩
private theorem pr2013779 : Nat.Prime 2013779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv73,pv1061]) (by decide +kernel)
def pv2013779 : PrimeValue := ⟨2013779, pr2013779⟩
private theorem pr2013821 : Nat.Prime 2013821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv5923]) (by decide +kernel)
def pv2013821 : PrimeValue := ⟨2013821, pr2013821⟩
private theorem pr2013911 : Nat.Prime 2013911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv37,pv5443]) (by decide +kernel)
def pv2013911 : PrimeValue := ⟨2013911, pr2013911⟩
private theorem pr2013941 : Nat.Prime 2013941 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv101,pv997]) (by decide +kernel)
def pv2013941 : PrimeValue := ⟨2013941, pr2013941⟩
private theorem pr2014139 : Nat.Prime 2014139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv47,pv3061]) (by decide +kernel)
def pv2014139 : PrimeValue := ⟨2014139, pr2014139⟩
private theorem pr2014301 : Nat.Prime 2014301 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv20143]) (by decide +kernel)
def pv2014301 : PrimeValue := ⟨2014301, pr2014301⟩
private theorem pr2014553 : Nat.Prime 2014553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv419,pv601]) (by decide +kernel)
def pv2014553 : PrimeValue := ⟨2014553, pr2014553⟩
private theorem pr2014739 : Nat.Prime 2014739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv5387]) (by decide +kernel)
def pv2014739 : PrimeValue := ⟨2014739, pr2014739⟩
private theorem pr2014979 : Nat.Prime 2014979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv709]) (by decide +kernel)
def pv2014979 : PrimeValue := ⟨2014979, pr2014979⟩
private theorem pr2015063 : Nat.Prime 2015063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv31,pv4643]) (by decide +kernel)
def pv2015063 : PrimeValue := ⟨2015063, pr2015063⟩
private theorem pr2015423 : Nat.Prime 2015423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv1007711]) (by decide +kernel)
def pv2015423 : PrimeValue := ⟨2015423, pr2015423⟩
private theorem pr2015609 : Nat.Prime 2015609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv35993]) (by decide +kernel)
def pv2015609 : PrimeValue := ⟨2015609, pr2015609⟩
private theorem pr2015633 : Nat.Prime 2015633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv263,pv479]) (by decide +kernel)
def pv2015633 : PrimeValue := ⟨2015633, pr2015633⟩
private theorem pr2015771 : Nat.Prime 2015771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv201577]) (by decide +kernel)
def pv2015771 : PrimeValue := ⟨2015771, pr2015771⟩
private theorem pr2015879 : Nat.Prime 2015879 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv1007939]) (by decide +kernel)
def pv2015879 : PrimeValue := ⟨2015879, pr2015879⟩
private theorem pr2015921 : Nat.Prime 2015921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv113,pv223]) (by decide +kernel)
def pv2015921 : PrimeValue := ⟨2015921, pr2015921⟩
private theorem pr2016029 : Nat.Prime 2016029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv89,pv809]) (by decide +kernel)
def pv2016029 : PrimeValue := ⟨2016029, pr2016029⟩
private theorem pr2016419 : Nat.Prime 2016419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv1008209]) (by decide +kernel)
def pv2016419 : PrimeValue := ⟨2016419, pr2016419⟩
private theorem pr2016461 : Nat.Prime 2016461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv100823]) (by decide +kernel)
def pv2016461 : PrimeValue := ⟨2016461, pr2016461⟩
private theorem pr2016653 : Nat.Prime 2016653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv45833]) (by decide +kernel)
def pv2016653 : PrimeValue := ⟨2016653, pr2016653⟩
private theorem pr2016671 : Nat.Prime 2016671 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv201667]) (by decide +kernel)
def pv2016671 : PrimeValue := ⟨2016671, pr2016671⟩
private theorem pr2017289 : Nat.Prime 2017289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv17,pv163]) (by decide +kernel)
def pv2017289 : PrimeValue := ⟨2017289, pr2017289⟩
private theorem pr2017601 : Nat.Prime 2017601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv97]) (by decide +kernel)
def pv2017601 : PrimeValue := ⟨2017601, pr2017601⟩
private theorem pr2017811 : Nat.Prime 2017811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv201781]) (by decide +kernel)
def pv2017811 : PrimeValue := ⟨2017811, pr2017811⟩
private theorem pr2017901 : Nat.Prime 2017901 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv1187]) (by decide +kernel)
def pv2017901 : PrimeValue := ⟨2017901, pr2017901⟩
private theorem pr2017919 : Nat.Prime 2017919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv59,pv349]) (by decide +kernel)
def pv2017919 : PrimeValue := ⟨2017919, pr2017919⟩
private theorem pr2018381 : Nat.Prime 2018381 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv13,pv1109]) (by decide +kernel)
def pv2018381 : PrimeValue := ⟨2018381, pr2018381⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
