/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table164
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table164.pv201359
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table038
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr201359 : PrimeCertificate 201359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv83,pv1213]) (by decide +kernel)
def pv201359 : PrimeValue := ⟨201359, pr201359⟩
private theorem pr201389 : PrimeCertificate 201389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv199]) (by decide +kernel)
def pv201389 : PrimeValue := ⟨201389, pr201389⟩
private theorem pr201497 : PrimeCertificate 201497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv283]) (by decide +kernel)
def pv201497 : PrimeValue := ⟨201497, pr201497⟩
private theorem pr201499 : PrimeCertificate 201499 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv43,pv71]) (by decide +kernel)
def pv201499 : PrimeValue := ⟨201499, pr201499⟩
private theorem pr201511 : PrimeCertificate 201511 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv2239]) (by decide +kernel)
def pv201511 : PrimeValue := ⟨201511, pr201511⟩
private theorem pr201557 : PrimeCertificate 201557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv1229]) (by decide +kernel)
def pv201557 : PrimeValue := ⟨201557, pr201557⟩
private theorem pr201611 : PrimeCertificate 201611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv20161]) (by decide +kernel)
def pv201611 : PrimeValue := ⟨201611, pr201611⟩
private theorem pr201767 : PrimeCertificate 201767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79,pv1277]) (by decide +kernel)
def pv201767 : PrimeValue := ⟨201767, pr201767⟩
private theorem pr201809 : PrimeCertificate 201809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12613]) (by decide +kernel)
def pv201809 : PrimeValue := ⟨201809, pr201809⟩
private theorem pr201829 : PrimeCertificate 201829 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv139]) (by decide +kernel)
def pv201829 : PrimeValue := ⟨201829, pr201829⟩
private theorem pr201979 : PrimeCertificate 201979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv229]) (by decide +kernel)
def pv201979 : PrimeValue := ⟨201979, pr201979⟩
private theorem pr202063 : PrimeCertificate 202063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv283]) (by decide +kernel)
def pv202063 : PrimeValue := ⟨202063, pr202063⟩
private theorem pr202127 : PrimeCertificate 202127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv101063]) (by decide +kernel)
def pv202127 : PrimeValue := ⟨202127, pr202127⟩
private theorem pr202289 : PrimeCertificate 202289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv269]) (by decide +kernel)
def pv202289 : PrimeValue := ⟨202289, pr202289⟩
private theorem pr202309 : PrimeCertificate 202309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv733]) (by decide +kernel)
def pv202309 : PrimeValue := ⟨202309, pr202309⟩
private theorem pr202357 : PrimeCertificate 202357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv73]) (by decide +kernel)
def pv202357 : PrimeValue := ⟨202357, pr202357⟩
private theorem pr202387 : PrimeCertificate 202387 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv89,pv379]) (by decide +kernel)
def pv202387 : PrimeValue := ⟨202387, pr202387⟩
private theorem pr202393 : PrimeCertificate 202393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv937]) (by decide +kernel)
def pv202393 : PrimeValue := ⟨202393, pr202393⟩
private theorem pr202549 : PrimeCertificate 202549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16879]) (by decide +kernel)
def pv202549 : PrimeValue := ⟨202549, pr202549⟩
private theorem pr202679 : PrimeCertificate 202679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv31,pv467]) (by decide +kernel)
def pv202679 : PrimeValue := ⟨202679, pr202679⟩
private theorem pr202729 : PrimeCertificate 202729 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv8447]) (by decide +kernel)
def pv202729 : PrimeValue := ⟨202729, pr202729⟩
private theorem pr202777 : PrimeCertificate 202777 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv17,pv71]) (by decide +kernel)
def pv202777 : PrimeValue := ⟨202777, pr202777⟩
private theorem pr202877 : PrimeCertificate 202877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv757]) (by decide +kernel)
def pv202877 : PrimeValue := ⟨202877, pr202877⟩
private theorem pr202879 : PrimeCertificate 202879 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv202879 : PrimeValue := ⟨202879, pr202879⟩
private theorem pr203011 : PrimeCertificate 203011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv67,pv101]) (by decide +kernel)
def pv203011 : PrimeValue := ⟨203011, pr203011⟩
private theorem pr203207 : PrimeCertificate 203207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv101603]) (by decide +kernel)
def pv203207 : PrimeValue := ⟨203207, pr203207⟩
private theorem pr203221 : PrimeCertificate 203221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1129]) (by decide +kernel)
def pv203221 : PrimeValue := ⟨203221, pr203221⟩
private theorem pr203321 : PrimeCertificate 203321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv17,pv23]) (by decide +kernel)
def pv203321 : PrimeValue := ⟨203321, pr203321⟩
private theorem pr203323 : PrimeCertificate 203323 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv47,pv103]) (by decide +kernel)
def pv203323 : PrimeValue := ⟨203323, pr203323⟩
private theorem pr203341 : PrimeCertificate 203341 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv3389]) (by decide +kernel)
def pv203341 : PrimeValue := ⟨203341, pr203341⟩
private theorem pr203383 : PrimeCertificate 203383 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11299]) (by decide +kernel)
def pv203383 : PrimeValue := ⟨203383, pr203383⟩
private theorem pr203387 : PrimeCertificate 203387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101693]) (by decide +kernel)
def pv203387 : PrimeValue := ⟨203387, pr203387⟩
private theorem pr203393 : PrimeCertificate 203393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv227]) (by decide +kernel)
def pv203393 : PrimeValue := ⟨203393, pr203393⟩
private theorem pr203531 : PrimeCertificate 203531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv20353]) (by decide +kernel)
def pv203531 : PrimeValue := ⟨203531, pr203531⟩
private theorem pr203627 : PrimeCertificate 203627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv53,pv113]) (by decide +kernel)
def pv203627 : PrimeValue := ⟨203627, pr203627⟩
private theorem pr203641 : PrimeCertificate 203641 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv1697]) (by decide +kernel)
def pv203641 : PrimeValue := ⟨203641, pr203641⟩
private theorem pr203663 : PrimeCertificate 203663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79,pv1289]) (by decide +kernel)
def pv203663 : PrimeValue := ⟨203663, pr203663⟩
private theorem pr203809 : PrimeCertificate 203809 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv193]) (by decide +kernel)
def pv203809 : PrimeValue := ⟨203809, pr203809⟩
private theorem pr203857 : PrimeCertificate 203857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv137]) (by decide +kernel)
def pv203857 : PrimeValue := ⟨203857, pr203857⟩
private theorem pr203869 : PrimeCertificate 203869 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv809]) (by decide +kernel)
def pv203869 : PrimeValue := ⟨203869, pr203869⟩
private theorem pr203969 : PrimeCertificate 203969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3187]) (by decide +kernel)
def pv203969 : PrimeValue := ⟨203969, pr203969⟩
private theorem pr204007 : PrimeCertificate 204007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv281]) (by decide +kernel)
def pv204007 : PrimeValue := ⟨204007, pr204007⟩
private theorem pr204047 : PrimeCertificate 204047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv102023]) (by decide +kernel)
def pv204047 : PrimeValue := ⟨204047, pr204047⟩
private theorem pr204481 : PrimeCertificate 204481 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv204481 : PrimeValue := ⟨204481, pr204481⟩
private theorem pr204511 : PrimeCertificate 204511 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv401]) (by decide +kernel)
def pv204511 : PrimeValue := ⟨204511, pr204511⟩
private theorem pr204599 : PrimeCertificate 204599 :=
  certifyPrime (q := pv13) (ls := [pv2,pv102299]) (by decide +kernel)
def pv204599 : PrimeValue := ⟨204599, pr204599⟩
private theorem pr204719 : PrimeCertificate 204719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv102359]) (by decide +kernel)
def pv204719 : PrimeValue := ⟨204719, pr204719⟩
private theorem pr204751 : PrimeCertificate 204751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv204751 : PrimeValue := ⟨204751, pr204751⟩
private theorem pr204791 : PrimeCertificate 204791 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv20479]) (by decide +kernel)
def pv204791 : PrimeValue := ⟨204791, pr204791⟩
private theorem pr204857 : PrimeCertificate 204857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv883]) (by decide +kernel)
def pv204857 : PrimeValue := ⟨204857, pr204857⟩
private theorem pr204917 : PrimeCertificate 204917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv51229]) (by decide +kernel)
def pv204917 : PrimeValue := ⟨204917, pr204917⟩
private theorem pr204923 : PrimeCertificate 204923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv102461]) (by decide +kernel)
def pv204923 : PrimeValue := ⟨204923, pr204923⟩
private theorem pr204931 : PrimeCertificate 204931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv204931 : PrimeValue := ⟨204931, pr204931⟩
private theorem pr204973 : PrimeCertificate 204973 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv29,pv31]) (by decide +kernel)
def pv204973 : PrimeValue := ⟨204973, pr204973⟩
private theorem pr205129 : PrimeCertificate 205129 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv37]) (by decide +kernel)
def pv205129 : PrimeValue := ⟨205129, pr205129⟩
private theorem pr205157 : PrimeCertificate 205157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv431]) (by decide +kernel)
def pv205157 : PrimeValue := ⟨205157, pr205157⟩
private theorem pr205339 : PrimeCertificate 205339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv4889]) (by decide +kernel)
def pv205339 : PrimeValue := ⟨205339, pr205339⟩
private theorem pr205397 : PrimeCertificate 205397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv51349]) (by decide +kernel)
def pv205397 : PrimeValue := ⟨205397, pr205397⟩
private theorem pr205433 : PrimeCertificate 205433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv25679]) (by decide +kernel)
def pv205433 : PrimeValue := ⟨205433, pr205433⟩
private theorem pr205483 : PrimeCertificate 205483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1489]) (by decide +kernel)
def pv205483 : PrimeValue := ⟨205483, pr205483⟩
private theorem pr205487 : PrimeCertificate 205487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv127,pv809]) (by decide +kernel)
def pv205487 : PrimeValue := ⟨205487, pr205487⟩
private theorem pr205607 : PrimeCertificate 205607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv223,pv461]) (by decide +kernel)
def pv205607 : PrimeValue := ⟨205607, pr205607⟩
private theorem pr205759 : PrimeCertificate 205759 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv23,pv71]) (by decide +kernel)
def pv205759 : PrimeValue := ⟨205759, pr205759⟩
private theorem pr205817 : PrimeCertificate 205817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1979]) (by decide +kernel)
def pv205817 : PrimeValue := ⟨205817, pr205817⟩
private theorem pr205883 : PrimeCertificate 205883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv311,pv331]) (by decide +kernel)
def pv205883 : PrimeValue := ⟨205883, pr205883⟩
private theorem pr206077 : PrimeCertificate 206077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1321]) (by decide +kernel)
def pv206077 : PrimeValue := ⟨206077, pr206077⟩
private theorem pr206083 : PrimeCertificate 206083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv206083 : PrimeValue := ⟨206083, pr206083⟩
private theorem pr206279 : PrimeCertificate 206279 :=
  certifyPrime (q := pv13) (ls := [pv2,pv17,pv6067]) (by decide +kernel)
def pv206279 : PrimeValue := ⟨206279, pr206279⟩
private theorem pr206351 : PrimeCertificate 206351 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv4127]) (by decide +kernel)
def pv206351 : PrimeValue := ⟨206351, pr206351⟩
private theorem pr206411 : PrimeCertificate 206411 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv20641]) (by decide +kernel)
def pv206411 : PrimeValue := ⟨206411, pr206411⟩
private theorem pr206413 : PrimeCertificate 206413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103,pv167]) (by decide +kernel)
def pv206413 : PrimeValue := ⟨206413, pr206413⟩
private theorem pr206489 : PrimeCertificate 206489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv487]) (by decide +kernel)
def pv206489 : PrimeValue := ⟨206489, pr206489⟩
private theorem pr206551 : PrimeCertificate 206551 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv206551 : PrimeValue := ⟨206551, pr206551⟩
private theorem pr206627 : PrimeCertificate 206627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv14759]) (by decide +kernel)
def pv206627 : PrimeValue := ⟨206627, pr206627⟩
private theorem pr206699 : PrimeCertificate 206699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103349]) (by decide +kernel)
def pv206699 : PrimeValue := ⟨206699, pr206699⟩
private theorem pr206807 : PrimeCertificate 206807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv1951]) (by decide +kernel)
def pv206807 : PrimeValue := ⟨206807, pr206807⟩
private theorem pr206819 : PrimeCertificate 206819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103409]) (by decide +kernel)
def pv206819 : PrimeValue := ⟨206819, pr206819⟩
private theorem pr206917 : PrimeCertificate 206917 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv43,pv401]) (by decide +kernel)
def pv206917 : PrimeValue := ⟨206917, pr206917⟩
private theorem pr206951 : PrimeCertificate 206951 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv4139]) (by decide +kernel)
def pv206951 : PrimeValue := ⟨206951, pr206951⟩
private theorem pr207029 : PrimeCertificate 207029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv709]) (by decide +kernel)
def pv207029 : PrimeValue := ⟨207029, pr207029⟩
private theorem pr207197 : PrimeCertificate 207197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv277]) (by decide +kernel)
def pv207197 : PrimeValue := ⟨207197, pr207197⟩
private theorem pr207227 : PrimeCertificate 207227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103613]) (by decide +kernel)
def pv207227 : PrimeValue := ⟨207227, pr207227⟩
private theorem pr207239 : PrimeCertificate 207239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv103619]) (by decide +kernel)
def pv207239 : PrimeValue := ⟨207239, pr207239⟩
private theorem pr207287 : PrimeCertificate 207287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv103643]) (by decide +kernel)
def pv207287 : PrimeValue := ⟨207287, pr207287⟩
private theorem pr207331 : PrimeCertificate 207331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv6911]) (by decide +kernel)
def pv207331 : PrimeValue := ⟨207331, pr207331⟩
private theorem pr207491 : PrimeCertificate 207491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv20749]) (by decide +kernel)
def pv207491 : PrimeValue := ⟨207491, pr207491⟩
private theorem pr207497 : PrimeCertificate 207497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv701]) (by decide +kernel)
def pv207497 : PrimeValue := ⟨207497, pr207497⟩
private theorem pr207521 : PrimeCertificate 207521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1297]) (by decide +kernel)
def pv207521 : PrimeValue := ⟨207521, pr207521⟩
private theorem pr207719 : PrimeCertificate 207719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv37,pv401]) (by decide +kernel)
def pv207719 : PrimeValue := ⟨207719, pr207719⟩
private theorem pr207799 : PrimeCertificate 207799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv587]) (by decide +kernel)
def pv207799 : PrimeValue := ⟨207799, pr207799⟩
private theorem pr207923 : PrimeCertificate 207923 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv727]) (by decide +kernel)
def pv207923 : PrimeValue := ⟨207923, pr207923⟩
private theorem pr207947 : PrimeCertificate 207947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv601]) (by decide +kernel)
def pv207947 : PrimeValue := ⟨207947, pr207947⟩
private theorem pr207971 : PrimeCertificate 207971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2971]) (by decide +kernel)
def pv207971 : PrimeValue := ⟨207971, pr207971⟩
private theorem pr208009 : PrimeCertificate 208009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv208009 : PrimeValue := ⟨208009, pr208009⟩
private theorem pr208037 : PrimeCertificate 208037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv52009]) (by decide +kernel)
def pv208037 : PrimeValue := ⟨208037, pr208037⟩
private theorem pr208067 : PrimeCertificate 208067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv104033]) (by decide +kernel)
def pv208067 : PrimeValue := ⟨208067, pr208067⟩
private theorem pr208099 : PrimeCertificate 208099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1051]) (by decide +kernel)
def pv208099 : PrimeValue := ⟨208099, pr208099⟩
private theorem pr208139 : PrimeCertificate 208139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv14867]) (by decide +kernel)
def pv208139 : PrimeValue := ⟨208139, pr208139⟩
private theorem pr208261 : PrimeCertificate 208261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv89]) (by decide +kernel)
def pv208261 : PrimeValue := ⟨208261, pr208261⟩
private theorem pr208283 : PrimeCertificate 208283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv223,pv467]) (by decide +kernel)
def pv208283 : PrimeValue := ⟨208283, pr208283⟩
private theorem pr208393 : PrimeCertificate 208393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv457]) (by decide +kernel)
def pv208393 : PrimeValue := ⟨208393, pr208393⟩
private theorem pr208409 : PrimeCertificate 208409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv109,pv239]) (by decide +kernel)
def pv208409 : PrimeValue := ⟨208409, pr208409⟩
private theorem pr208489 : PrimeCertificate 208489 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv17,pv73]) (by decide +kernel)
def pv208489 : PrimeValue := ⟨208489, pr208489⟩
private theorem pr208529 : PrimeCertificate 208529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13033]) (by decide +kernel)
def pv208529 : PrimeValue := ⟨208529, pr208529⟩
private theorem pr208609 : PrimeCertificate 208609 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv41,pv53]) (by decide +kernel)
def pv208609 : PrimeValue := ⟨208609, pr208609⟩
private theorem pr208721 : PrimeCertificate 208721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2609]) (by decide +kernel)
def pv208721 : PrimeValue := ⟨208721, pr208721⟩
private theorem pr208729 : PrimeCertificate 208729 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv223]) (by decide +kernel)
def pv208729 : PrimeValue := ⟨208729, pr208729⟩
private theorem pr208799 : PrimeCertificate 208799 :=
  certifyPrime (q := pv13) (ls := [pv2,pv104399]) (by decide +kernel)
def pv208799 : PrimeValue := ⟨208799, pr208799⟩
private theorem pr208907 : PrimeCertificate 208907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv1559]) (by decide +kernel)
def pv208907 : PrimeValue := ⟨208907, pr208907⟩
private theorem pr209459 : PrimeCertificate 209459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv104729]) (by decide +kernel)
def pv209459 : PrimeValue := ⟨209459, pr209459⟩
private theorem pr209497 : PrimeCertificate 209497 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv29,pv43]) (by decide +kernel)
def pv209497 : PrimeValue := ⟨209497, pr209497⟩
private theorem pr209563 : PrimeCertificate 209563 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv53,pv659]) (by decide +kernel)
def pv209563 : PrimeValue := ⟨209563, pr209563⟩
private theorem pr209569 : PrimeCertificate 209569 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv37,pv59]) (by decide +kernel)
def pv209569 : PrimeValue := ⟨209569, pr209569⟩
private theorem pr209719 : PrimeCertificate 209719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv191]) (by decide +kernel)
def pv209719 : PrimeValue := ⟨209719, pr209719⟩
private theorem pr209743 : PrimeCertificate 209743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv2689]) (by decide +kernel)
def pv209743 : PrimeValue := ⟨209743, pr209743⟩
private theorem pr209887 : PrimeCertificate 209887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv34981]) (by decide +kernel)
def pv209887 : PrimeValue := ⟨209887, pr209887⟩
private theorem pr209953 : PrimeCertificate 209953 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3]) (by decide +kernel)
def pv209953 : PrimeValue := ⟨209953, pr209953⟩
private theorem pr210031 : PrimeCertificate 210031 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7001]) (by decide +kernel)
def pv210031 : PrimeValue := ⟨210031, pr210031⟩
private theorem pr210101 : PrimeCertificate 210101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv191]) (by decide +kernel)
def pv210101 : PrimeValue := ⟨210101, pr210101⟩
private theorem pr210461 : PrimeCertificate 210461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv619]) (by decide +kernel)
def pv210461 : PrimeValue := ⟨210461, pr210461⟩
private theorem pr210491 : PrimeCertificate 210491 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv31,pv97]) (by decide +kernel)
def pv210491 : PrimeValue := ⟨210491, pr210491⟩
private theorem pr210599 : PrimeCertificate 210599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv29,pv3631]) (by decide +kernel)
def pv210599 : PrimeValue := ⟨210599, pr210599⟩
private theorem pr210929 : PrimeCertificate 210929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13183]) (by decide +kernel)
def pv210929 : PrimeValue := ⟨210929, pr210929⟩
private theorem pr210943 : PrimeCertificate 210943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11719]) (by decide +kernel)
def pv210943 : PrimeValue := ⟨210943, pr210943⟩
private theorem pr211061 : PrimeCertificate 211061 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv61,pv173]) (by decide +kernel)
def pv211061 : PrimeValue := ⟨211061, pr211061⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
