/- GID: D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates
   generality: S
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates
   mirror-E: none(waiver:kernel-replayed-geometric-certificate)
   anchors: []
   digest: Certify complete selected geometric transitions for the radius-four controller. -/

import D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
import D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourCertificates

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.BranchingPotential
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourData

-- A balanced tree in both mask-code and original-row-index order. Literal payloads
-- are the lossless expansion of AdaptiveRadiusFourData's increments and weight tags.
private inductive LookupTree where
  | empty
  | node (code index weight action : ℕ) (left right : LookupTree)

private def LookupTree.find (code : ℕ) : LookupTree → Option (Fin 881)
  | .empty => none
  | .node key index _ _ left right =>
      if code < key then left.find code
      else if key < code then right.find code
      else if h : index < 881 then some ⟨index, h⟩ else none

private def LookupTree.getRow (index : ℕ) : LookupTree → ℕ × ℕ × ℕ
  | .empty => (0, 0, 0)
  | .node code key weight action left right =>
      if index < key then left.getRow index
      else if key < index then right.getRow index
      else (code, weight, action)

private def lookupTree : LookupTree :=
  (.node 2653438 440 28616 0
    (.node 530927 220 53468 0
      (.node 12776 110 77502 1
        (.node 5365 55 75242 0
          (.node 4335 27 82896 0
            (.node 4197 13 88747 0 (.node 4174 6 88406 0 (.node 4165 3 93735 0 (.node 4160 1 95380 0 (.node 4096 0 100000 0 .empty .empty) (.node 4164 2 93735 0 .empty .empty)) (.node 4173 5 91070 0 (.node 4167 4 91070 1 .empty .empty) .empty)) (.node 4183 10 86626 1 (.node 4181 8 88419 0 (.node 4175 7 88406 0 .empty .empty) (.node 4182 9 86626 1 .empty .empty)) (.node 4191 12 83962 0 (.node 4190 11 83962 0 .empty .empty) .empty))) (.node 4293 20 88747 0 (.node 4207 17 85651 0 (.node 4205 15 86106 0 (.node 4199 14 88292 0 .empty .empty) (.node 4206 16 85651 0 .empty .empty)) (.node 4223 19 82769 0 (.node 4222 18 82769 0 .empty .empty) .empty)) (.node 4303 24 85651 0 (.node 4301 22 88292 0 (.node 4295 21 86106 0 .empty .empty) (.node 4302 23 85651 0 .empty .empty)) (.node 4324 26 83800 1 (.node 4320 25 84015 0 .empty .empty) .empty))))
            (.node 4854 41 75446 0 (.node 4558 34 82770 0 (.node 4429 31 86626 0 (.node 4421 29 88419 0 (.node 4336 28 80660 0 .empty .empty) (.node 4428 30 86626 0 .empty .empty)) (.node 4431 33 83962 0 (.node 4430 32 83962 0 .empty .empty) .empty)) (.node 4848 38 75553 0 (.node 4576 36 80661 0 (.node 4559 35 82770 0 .empty .empty) (.node 4580 37 80553 1 .empty .empty)) (.node 4852 40 75446 0 (.node 4850 39 75553 0 .empty .empty) .empty))) (.node 5245 48 77545 0 (.node 5215 45 78286 0 (.node 5199 43 80000 0 (.node 5198 42 80000 0 .empty .empty) (.node 5214 44 78286 0 .empty .empty)) (.node 5242 47 77577 0 (.node 5231 46 77790 0 .empty .empty) .empty)) (.node 5360 52 75350 0 (.node 5247 50 77545 0 (.node 5246 49 77545 0 .empty .empty) (.node 5351 51 75488 0 .empty .empty)) (.node 5364 54 75242 0 (.node 5362 53 75350 0 .empty .empty) .empty)))))
          (.node 6886 83 75538 0
            (.node 6375 69 79030 0 (.node 6254 62 81323 0 (.node 5874 59 73622 0 (.node 5367 57 75242 0 (.node 5366 56 75242 0 .empty .empty) (.node 5872 58 73622 0 .empty .empty)) (.node 6222 61 81718 0 (.node 5878 60 73515 0 .empty .empty) .empty)) (.node 6370 66 79137 0 (.node 6271 64 79688 0 (.node 6255 63 81323 0 .empty .empty) (.node 6343 65 79427 0 .empty .empty)) (.node 6374 68 79030 0 (.node 6371 67 79137 0 .empty .empty) .empty))) (.node 6391 76 77395 0 (.node 6387 73 77502 0 (.node 6383 71 78578 0 (.node 6382 70 78578 0 .empty .empty) (.node 6386 72 77502 0 .empty .empty)) (.node 6390 75 77395 0 (.node 6389 74 77438 0 .empty .empty) .empty)) (.node 6511 80 76879 0 (.node 6399 78 76943 0 (.node 6398 77 76943 0 .empty .empty) (.node 6510 79 76879 0 .empty .empty)) (.node 6639 82 75697 0 (.node 6638 81 75697 0 .empty .empty) .empty))))
            (.node 12495 97 81323 0 (.node 7422 90 74309 0 (.node 7406 87 74555 0 (.node 6900 85 74333 0 (.node 6896 84 74441 0 .empty .empty) (.node 6902 86 74333 0 .empty .empty)) (.node 7415 89 74761 0 (.node 7414 88 74761 0 .empty .empty) .empty)) (.node 12366 94 81718 0 (.node 7920 92 73141 0 (.node 7423 91 74309 0 .empty .empty) (.node 7926 93 73033 0 .empty .empty)) (.node 12494 96 81323 0 (.node 12397 95 79427 0 .empty .empty) .empty))) (.node 12526 104 78578 1 (.node 12521 101 79137 0 (.node 12511 99 76879 0 (.node 12510 98 76879 0 .empty .empty) (.node 12520 100 79137 0 .empty .empty)) (.node 12525 103 79030 1 (.node 12524 102 79030 1 .empty .empty) .empty)) (.node 12543 107 75696 0 (.node 12542 106 75696 0 (.node 12527 105 78578 1 .empty .empty) .empty) (.node 12773 109 77438 1 (.node 12751 108 79688 1 .empty .empty) .empty))))))
        (.node 147008 165 62636 0
          (.node 20965 138 75242 1
            (.node 15360 124 71596 1 (.node 14400 117 76041 1 (.node 12782 114 76943 0 (.node 12780 112 77395 1 (.node 12777 111 77502 1 .empty .empty) (.node 12781 113 77395 1 .empty .empty)) (.node 14336 116 76659 0 (.node 12783 115 76943 0 .empty .empty) .empty)) (.node 14831 121 72624 1 (.node 14591 119 72624 0 (.node 14590 118 72624 0 .empty .empty) (.node 14830 120 72624 1 .empty .empty)) (.node 14847 123 70989 0 (.node 14846 122 70989 0 .empty .empty) .empty))) (.node 20815 131 78286 1 (.node 20687 128 77790 1 (.node 15888 126 69497 0 (.node 15872 125 69555 0 .empty .empty) (.node 20559 127 80000 1 .empty .empty)) (.node 20814 130 78286 1 (.node 20717 129 75488 1 .empty .empty) .empty)) (.node 20943 135 77545 1 (.node 20938 133 77577 1 (.node 20935 132 77545 1 .empty .empty) (.node 20942 134 77545 1 .empty .empty)) (.node 20964 137 75242 1 (.node 20960 136 75350 1 .empty .empty) .empty))))
            (.node 53732 152 73515 1 (.node 29167 145 74310 1 (.node 29164 142 74761 1 (.node 20973 140 75242 1 (.node 20972 139 75242 1 .empty .empty) (.node 28910 141 74555 1 .empty .empty)) (.node 29166 144 74310 1 (.node 29165 143 74761 1 .empty .empty) .empty)) (.node 45292 149 75538 1 (.node 37348 147 75446 1 (.node 30784 146 71287 0 .empty .empty) (.node 37356 148 75446 1 .empty .empty)) (.node 45548 151 74333 1 (.node 45540 150 74333 1 .empty .empty) .empty))) (.node 63808 159 69189 1 (.node 61932 156 73034 1 (.node 61920 154 73141 1 (.node 53740 153 73515 1 .empty .empty) (.node 61924 155 73034 1 .empty .empty)) (.node 63552 158 69246 1 (.node 63488 157 69555 1 .empty .empty) .empty)) (.node 146960 162 62945 0 (.node 146944 161 62945 0 (.node 146514 160 62716 0 .empty .empty) .empty) (.node 146992 164 62945 0 (.node 146976 163 62945 0 .empty .empty) .empty)))))
          (.node 277616 193 59854 0
            (.node 269046 179 63599 0 (.node 266996 172 64491 0 (.node 266480 169 66850 0 (.node 147026 167 62636 0 (.node 147010 166 62636 0 .empty .empty) (.node 147056 168 62636 0 .empty .empty)) (.node 266994 171 64598 0 (.node 266992 170 64598 0 .empty .empty) .empty)) (.node 268018 176 63874 0 (.node 267510 174 64032 0 (.node 267504 173 64139 0 .empty .empty) (.node 268016 175 63874 0 .empty .empty)) (.node 268534 178 63896 0 (.node 268022 177 63767 0 .empty .empty) .empty))) (.node 270070 186 63468 0 (.node 269558 183 63734 0 (.node 269526 181 63736 0 (.node 269490 180 63919 0 .empty .empty) (.node 269552 182 63841 0 .empty .empty)) (.node 270066 185 63575 0 (.node 270064 184 63575 0 .empty .empty) .empty)) (.node 277584 190 59854 0 (.node 277520 188 60163 0 (.node 276598 187 60017 0 .empty .empty) (.node 277552 189 60163 0 .empty .empty)) (.node 277590 192 59854 0 (.node 277586 191 59854 0 .empty .empty) .empty))))
            (.node 408688 207 58507 0 (.node 278100 200 59588 0 (.node 278048 197 59904 0 (.node 277622 195 59854 0 (.node 277618 194 59854 0 .empty .empty) (.node 278016 196 59904 0 .empty .empty)) (.node 278098 199 59588 0 (.node 278096 198 59588 0 .empty .empty) .empty)) (.node 278130 204 59588 0 (.node 278118 202 59595 0 (.node 278102 201 59588 0 .empty .empty) (.node 278128 203 59588 0 .empty .empty)) (.node 278134 206 59588 0 (.node 278132 205 59588 0 .empty .empty) .empty))) (.node 530662 214 56801 0 (.node 409200 211 58467 0 (.node 409104 209 58775 0 (.node 409088 208 58775 0 .empty .empty) (.node 409136 210 58775 0 .empty .empty)) (.node 529136 213 57068 0 (.node 409202 212 58467 0 .empty .empty) .empty)) (.node 530670 217 56349 0 (.node 530667 216 56365 0 (.node 530663 215 56801 0 .empty .empty) .empty) (.node 530926 219 53468 0 (.node 530671 218 56349 0 .empty .empty) .empty)))))))
      (.node 932880 330 50817 0
        (.node 539759 275 51769 0
          (.node 538983 248 50651 0
            (.node 538734 234 52428 0 (.node 532214 227 56142 0 (.node 531694 224 55690 0 (.node 530930 222 53554 0 (.node 530928 221 53554 0 .empty .empty) (.node 530938 223 53468 0 .empty .empty)) (.node 531711 226 55690 0 (.node 531710 225 55690 0 .empty .empty) .empty)) (.node 538722 231 52925 0 (.node 538656 229 53234 0 (.node 536702 228 52588 0 .empty .empty) (.node 538670 230 52667 0 .empty .empty)) (.node 538727 233 52925 0 (.node 538726 232 52925 0 .empty .empty) .empty))) (.node 538861 241 52035 0 (.node 538751 238 52428 0 (.node 538736 236 52925 0 (.node 538735 235 52428 0 .empty .empty) (.node 538738 237 52925 0 .empty .empty)) (.node 538859 240 52035 0 (.node 538851 239 52315 0 .empty .empty) .empty)) (.node 538875 245 52035 0 (.node 538863 243 52035 0 (.node 538862 242 52035 0 .empty .empty) (.node 538874 244 52035 0 .empty .empty)) (.node 538879 247 52035 0 (.node 538878 246 52035 0 .empty .empty) .empty))))
            (.node 539690 262 52008 0 (.node 539127 255 50443 0 (.node 539119 252 50400 0 (.node 538991 250 50603 0 (.node 538990 249 50603 0 .empty .empty) (.node 539118 251 50400 0 .empty .empty)) (.node 539126 254 50443 0 (.node 539122 253 50443 0 .empty .empty) .empty)) (.node 539134 259 50400 0 (.node 539130 257 50400 0 (.node 539128 256 50400 0 .empty .empty) (.node 539131 258 50400 0 .empty .empty)) (.node 539682 261 52575 0 (.node 539135 260 50400 0 .empty .empty) .empty))) (.node 539742 269 51786 0 (.node 539707 266 52008 0 (.node 539694 264 52008 0 (.node 539691 263 52008 0 .empty .empty) (.node 539695 265 52008 0 .empty .empty)) (.node 539711 268 52008 0 (.node 539710 267 52008 0 .empty .empty) .empty)) (.node 539747 272 52266 0 (.node 539746 271 52266 0 (.node 539744 270 52266 0 .empty .empty) .empty) (.node 539751 274 52266 0 (.node 539750 273 52266 0 .empty .empty) .empty)))))
          (.node 555514 303 47784 0
            (.node 540272 289 52266 0 (.node 539770 282 51769 0 (.node 539763 279 52266 0 (.node 539761 277 52266 0 (.node 539760 276 52266 0 .empty .empty) (.node 539762 278 52266 0 .empty .empty)) (.node 539767 281 52266 0 (.node 539766 280 52266 0 .empty .empty) .empty)) (.node 539890 286 51656 0 (.node 539774 284 51769 0 (.node 539771 283 51769 0 .empty .empty) (.node 539775 285 51769 0 .empty .empty)) (.node 540262 288 52266 0 (.node 539895 287 51656 0 .empty .empty) .empty))) (.node 547315 296 48260 0 (.node 540400 293 51656 0 (.node 540276 291 52266 0 (.node 540274 290 52266 0 .empty .empty) (.node 540278 292 52266 0 .empty .empty)) (.node 547314 295 48260 0 (.node 547067 294 48506 0 .empty .empty) .empty)) (.node 547326 300 48260 0 (.node 547322 298 48260 0 (.node 547318 297 48260 0 .empty .empty) (.node 547323 299 48260 0 .empty .empty)) (.node 555506 302 47784 0 (.node 555262 301 48029 0 .empty .empty) .empty))))
            (.node 801520 317 50694 0 (.node 670834 310 51032 0 (.node 669810 307 51518 0 (.node 555519 305 47784 0 (.node 555518 304 47784 0 .empty .empty) (.node 669808 306 51518 0 .empty .empty)) (.node 670322 309 51518 0 (.node 670320 308 51518 0 .empty .empty) .empty)) (.node 671330 314 51032 0 (.node 671248 312 51341 0 (.node 671232 311 51341 0 .empty .empty) (.node 671312 313 51032 0 .empty .empty)) (.node 671346 316 51032 0 (.node 671344 315 51032 0 .empty .empty) .empty))) (.node 802036 324 50595 0 (.node 801910 321 51205 0 (.node 801906 319 51205 0 (.node 801904 318 51205 0 .empty .empty) (.node 801908 320 51205 0 .empty .empty)) (.node 802034 323 50595 0 (.node 802032 322 50595 0 .empty .empty) .empty)) (.node 802422 327 51205 0 (.node 802418 326 51205 0 (.node 802038 325 50595 0 .empty .empty) .empty) (.node 802550 329 50595 0 (.node 802544 328 50595 0 .empty .empty) .empty))))))
        (.node 2111974 385 52035 0
          (.node 2111631 358 52667 0
            (.node 2109938 344 53468 0 (.node 2109677 337 56801 0 (.node 933488 334 50508 0 (.node 933376 332 50817 0 (.node 932976 331 50508 0 .empty .empty) (.node 933392 333 50817 0 .empty .empty)) (.node 2109675 336 56365 0 (.node 2103758 335 52588 0 .empty .empty) .empty)) (.node 2109695 341 53468 0 (.node 2109679 339 56349 0 (.node 2109678 338 56349 0 .empty .empty) (.node 2109694 340 53468 0 .empty .empty)) (.node 2109936 343 53554 0 (.node 2109932 342 56801 0 .empty .empty) .empty))) (.node 2110969 351 48260 0 (.node 2110964 348 48260 0 (.node 2110960 346 48260 0 (.node 2110955 345 48506 0 .empty .empty) (.node 2110962 347 48260 0 .empty .empty)) (.node 2110968 350 48260 0 (.node 2110966 349 48260 0 .empty .empty) .empty)) (.node 2111626 355 52667 0 (.node 2110974 353 48260 0 (.node 2110971 352 48260 0 .empty .empty) (.node 2111624 354 53234 0 .empty .empty)) (.node 2111630 357 52667 0 (.node 2111627 356 52667 0 .empty .empty) .empty))))
            (.node 2111726 372 52035 0 (.node 2111695 365 52428 0 (.node 2111692 362 52925 0 (.node 2111688 360 52925 0 (.node 2111680 359 52925 0 .empty .empty) (.node 2111689 361 52925 0 .empty .empty)) (.node 2111694 364 52428 0 (.node 2111693 363 52925 0 .empty .empty) .empty)) (.node 2111719 369 52035 0 (.node 2111710 367 50603 0 (.node 2111709 366 50651 0 .empty .empty) (.node 2111711 368 50603 0 .empty .empty)) (.node 2111723 371 52035 0 (.node 2111721 370 52315 0 .empty .empty) .empty))) (.node 2111944 379 52925 0 (.node 2111883 376 52667 0 (.node 2111742 374 50400 0 (.node 2111727 373 52035 0 .empty .empty) (.node 2111743 375 50400 0 .empty .empty)) (.node 2111936 378 52925 0 (.node 2111887 377 52667 0 .empty .empty) .empty)) (.node 2111949 382 52925 0 (.node 2111948 381 52925 0 (.node 2111945 380 52925 0 .empty .empty) .empty) (.node 2111970 384 52035 0 (.node 2111951 383 52428 0 .empty .empty) .empty)))))
          (.node 2128320 413 52266 0
            (.node 2113010 399 47783 0 (.node 2111994 392 50400 0 (.node 2111983 389 52035 0 (.node 2111979 387 52035 0 (.node 2111978 386 52035 0 .empty .empty) (.node 2111982 388 52035 0 .empty .empty)) (.node 2111988 391 50443 0 (.node 2111984 390 50443 0 .empty .empty) .empty)) (.node 2111999 396 50400 0 (.node 2111997 394 50443 0 (.node 2111995 393 50400 0 .empty .empty) (.node 2111998 395 50400 0 .empty .empty)) (.node 2113008 398 47783 0 (.node 2113006 397 48029 0 .empty .empty) .empty))) (.node 2128000 406 52575 0 (.node 2126062 403 55690 0 (.node 2113022 401 47783 0 (.node 2113014 400 47783 0 .empty .empty) (.node 2113023 402 47783 0 .empty .empty)) (.node 2126319 405 55690 0 (.node 2126318 404 55690 0 .empty .empty) .empty)) (.node 2128206 410 51786 0 (.node 2128073 408 52266 0 (.node 2128011 407 52008 0 .empty .empty) (.node 2128076 409 52266 0 .empty .empty)) (.node 2128271 412 52008 0 (.node 2128270 411 52008 0 .empty .empty) .empty))))
            (.node 2160844 427 52266 0 (.node 2128333 420 52266 0 (.node 2128330 417 51769 0 (.node 2128328 415 52266 0 (.node 2128321 414 52266 0 .empty .empty) (.node 2128329 416 52266 0 .empty .empty)) (.node 2128332 419 52266 0 (.node 2128331 418 51769 0 .empty .empty) .empty)) (.node 2128365 424 51656 0 (.node 2128335 422 51769 0 (.node 2128334 421 51769 0 .empty .empty) (.node 2128352 423 51656 0 .empty .empty)) (.node 2159084 426 56142 0 (.node 2134496 425 57068 0 .empty .empty) .empty))) (.node 2637054 434 29275 0 (.node 2161100 431 52266 0 (.node 2161092 429 52266 0 (.node 2161088 428 52266 0 .empty .empty) (.node 2161096 430 52266 0 .empty .empty)) (.node 2637050 433 29275 0 (.node 2161120 432 51656 0 .empty .empty) .empty)) (.node 2652642 437 29275 0 (.node 2637304 436 29275 0 (.node 2637298 435 29275 0 .empty .empty) .empty) (.node 2652656 439 29275 0 (.node 2652654 438 29275 0 .empty .empty) .empty))))))))
    (.node 1077967296 661 51533 0
      (.node 134487792 551 46560 3
        (.node 6355424 496 50595 0
          (.node 4248044 468 63767 1
            (.node 4223400 454 63919 1 (.node 4198884 447 66743 1 (.node 2653686 444 28616 0 (.node 2653680 442 28616 0 (.node 2653678 441 28616 0 .empty .empty) (.node 2653682 443 28616 0 .empty .empty)) (.node 2653694 446 28616 0 (.node 2653688 445 28616 0 .empty .empty) .empty)) (.node 4215268 451 64032 1 (.node 4209100 449 60017 1 (.node 4207084 448 63896 1 .empty .empty) (.node 4215264 450 64139 1 .empty .empty)) (.node 4223340 453 63736 1 (.node 4215276 452 64032 1 .empty .empty) .empty))) (.node 4225472 461 59854 1 (.node 4225348 458 59854 1 (.node 4223468 456 63734 1 (.node 4223456 455 63841 1 .empty .empty) (.node 4225344 457 59854 1 .empty .empty)) (.node 4225356 460 59854 1 (.node 4225352 459 59854 1 .empty .empty) .empty)) (.node 4231660 465 64491 1 (.node 4225484 463 59854 1 (.node 4225480 462 59854 1 .empty .empty) (.node 4231652 464 64491 1 .empty .empty)) (.node 4248036 467 63767 1 (.node 4239852 466 63599 1 .empty .empty) .empty))))
            (.node 4258244 482 59588 1 (.node 4257996 475 59595 1 (.node 4256236 472 63468 1 (.node 4256228 470 63468 1 (.node 4256224 469 63575 1 .empty .empty) (.node 4256232 471 63575 1 .empty .empty)) (.node 4257984 474 59595 1 (.node 4257856 473 59595 1 .empty .empty) .empty)) (.node 4258120 479 59588 1 (.node 4258112 477 59588 1 (.node 4258048 476 59897 1 .empty .empty) (.node 4258116 478 59588 1 .empty .empty)) (.node 4258240 481 59588 1 (.node 4258124 480 59588 1 .empty .empty) .empty))) (.node 6322656 489 50595 0 (.node 6322628 486 51205 0 (.node 4258252 484 59588 1 (.node 4258248 483 59588 1 .empty .empty) (.node 6322624 485 51205 0 .empty .empty)) (.node 6322636 488 51205 0 (.node 6322632 487 51205 0 .empty .empty) .empty)) (.node 6339040 493 50694 0 (.node 6322664 491 50595 0 (.node 6322660 490 50595 0 .empty .empty) (.node 6322668 492 50595 0 .empty .empty)) (.node 6355404 495 51205 0 (.node 6355400 494 51205 0 .empty .empty) .empty)))))
          (.node 14744000 524 50508 0
            (.node 10549448 510 51032 0 (.node 8452424 503 62636 1 (.node 8452168 500 62636 1 (.node 8419656 498 62716 1 (.node 6355436 497 50595 0 .empty .empty) (.node 8452160 499 62636 1 .empty .empty)) (.node 8452416 502 62636 1 (.node 8452288 501 62636 1 .empty .empty) .empty)) (.node 10533312 507 51518 0 (.node 10500552 505 51518 0 (.node 8452544 504 62636 1 .empty .empty) (.node 10516936 506 51032 0 .empty .empty)) (.node 10549312 509 51032 0 (.node 10533320 508 51518 0 .empty .empty) .empty))) (.node 12646848 517 58467 1 (.node 12614080 514 58507 1 (.node 10549696 512 51032 0 (.node 10549568 511 51032 0 .empty .empty) (.node 10549704 513 51032 0 .empty .empty)) (.node 12646720 516 58467 1 (.node 12646464 515 58467 1 .empty .empty) .empty)) (.node 14743616 521 50508 0 (.node 14711104 519 50508 0 (.node 12646856 518 58467 1 .empty .empty) (.node 14711232 520 50508 0 .empty .empty)) (.node 14743872 523 50508 0 (.node 14743808 522 50817 0 .empty .empty) .empty))))
            (.node 67911184 538 46868 0 (.node 67517552 531 51319 1 (.node 67255872 528 51611 1 (.node 67255808 526 51920 1 (.node 67124736 525 56368 1 .empty .empty) (.node 67255856 527 51920 1 .empty .empty)) (.node 67386480 530 51533 1 (.node 67386384 529 51841 1 .empty .empty) .empty)) (.node 67649136 535 46625 0 (.node 67518000 533 51627 1 (.node 67517952 532 51627 1 .empty .empty) (.node 67518064 534 51319 1 .empty .empty)) (.node 67910768 537 46559 0 (.node 67780208 536 46505 0 .empty .empty) .empty))) (.node 68042352 545 46452 0 (.node 68042240 542 46761 0 (.node 68041744 540 46761 0 (.node 67911280 539 46559 0 .empty .empty) (.node 68041840 541 46452 0 .empty .empty)) (.node 68042288 544 46761 0 (.node 68042256 543 46761 0 .empty .empty) .empty)) (.node 134485232 548 46567 3 (.node 134364672 547 47407 0 (.node 134225648 546 53926 4 .empty .empty) .empty) (.node 134487280 550 46560 3 (.node 134485744 549 46567 3 .empty .empty) .empty))))))
        (.node 470301728 606 20976 0
          (.node 202260080 579 42844 3
            (.node 201604112 565 43110 3 (.node 135019760 558 42844 0 (.node 134756448 555 43719 0 (.node 134626816 553 43719 3 (.node 134626416 552 43454 2 .empty .empty) (.node 134626832 554 43719 3 .empty .empty)) (.node 135018722 557 42844 0 (.node 134756578 556 43109 0 .empty .empty) .empty)) (.node 135151216 562 43453 0 (.node 135020272 560 42844 0 (.node 135019764 559 42844 0 .empty .empty) (.node 135151120 561 43719 3 .empty .empty)) (.node 201473536 564 43156 3 (.node 136845542 563 21134 0 .empty .empty) .empty))) (.node 201735280 572 42844 3 (.node 201604720 569 42844 3 (.node 201604608 567 43110 3 (.node 201604208 566 42844 3 .empty .empty) (.node 201604624 568 43110 3 .empty .empty)) (.node 201735184 571 43110 3 (.node 201735168 570 43110 3 .empty .empty) .empty)) (.node 202128496 576 42844 3 (.node 201735696 574 43110 3 (.node 201735680 573 43110 3 .empty .empty) (.node 201735792 575 42844 3 .empty .empty)) (.node 202259984 578 43109 3 (.node 202259568 577 42844 3 .empty .empty) .empty))))
            (.node 403192562 593 20395 0 (.node 271088120 586 1 0 (.node 271071736 583 1 0 (.node 271071714 581 1 0 (.node 269236978 580 20641 0 .empty .empty) (.node 271071730 582 1 0 .empty .empty)) (.node 271072754 585 1 0 (.node 271072738 584 1 0 .empty .empty) .empty)) (.node 336477728 590 21134 0 (.node 335821840 588 25987 1 (.node 274774504 587 20641 0 .empty .empty) (.node 336477712 589 21134 0 .empty .empty)) (.node 403192050 592 20395 0 (.node 403192034 591 20395 0 .empty .empty) .empty))) (.node 405281014 600 1 0 (.node 403455202 597 20395 0 (.node 403454178 595 20395 0 (.node 403193058 594 20395 0 .empty .empty) (.node 403454706 596 20395 0 .empty .empty)) (.node 405280998 599 1 0 (.node 403455218 598 20395 0 .empty .empty) .empty)) (.node 470039568 603 20976 0 (.node 405544166 602 1 0 (.node 405289058 601 1 0 .empty .empty) .empty) (.node 470300704 605 20976 0 (.node 470171152 604 20976 0 .empty .empty) .empty)))))
          (.node 549517312 634 43719 5
            (.node 538982632 620 43109 0 (.node 470693904 613 20976 0 (.node 470562848 610 20976 0 (.node 470433296 608 20976 0 (.node 470432800 607 20976 0 .empty .empty) (.node 470433312 609 20976 0 .empty .empty)) (.node 470563872 612 20976 0 (.node 470563856 611 20976 0 .empty .empty) .empty)) (.node 472128528 617 1 0 (.node 470695440 615 20976 0 (.node 470694944 614 20976 0 .empty .empty) (.node 470695456 616 20976 0 .empty .empty)) (.node 536932832 619 53926 2 (.node 472652816 618 1 0 .empty .empty) .empty))) (.node 541127136 627 46560 5 (.node 541086176 624 46567 5 (.node 538998976 622 43719 0 (.node 538982888 621 43109 0 .empty .empty) (.node 539505132 623 21134 0 .empty .empty)) (.node 541118944 626 46567 5 (.node 541094368 625 46560 5 .empty .empty) .empty)) (.node 543226336 631 42844 0 (.node 543193568 629 42844 0 (.node 543177192 628 42844 0 .empty .empty) (.node 543193572 630 42844 0 .empty .empty)) (.node 549484992 633 43454 4 (.node 545323008 632 47407 1 .empty .empty) .empty))))
            (.node 1007171680 648 11801 0 (.node 807451112 641 20395 0 (.node 807418088 638 20395 0 (.node 551614720 636 43719 2 (.node 549517568 635 43719 5 .empty .empty) (.node 551614912 637 43453 0 .empty .empty)) (.node 807434728 640 20395 0 (.node 807418344 639 20395 0 .empty .empty) .empty)) (.node 811629032 645 20395 0 (.node 807942344 643 1 0 (.node 807940588 642 1 0 .empty .empty) (.node 811612648 644 20395 0 .empty .empty)) (.node 812151276 647 1 0 (.node 811645416 646 20395 0 .empty .empty) .empty))) (.node 1013454880 655 1 0 (.node 1009268800 652 1 0 (.node 1009260576 650 1 0 (.node 1007434848 649 11801 0 .empty .empty) (.node 1009268768 651 1 0 .empty .empty)) (.node 1011365920 654 1 0 (.node 1009523744 653 1 0 .empty .empty) .empty)) (.node 1073805376 658 56059 0 (.node 1013463104 657 1 0 (.node 1013463072 656 1 0 .empty .empty) .empty) (.node 1077967168 660 51533 0 (.node 1075902912 659 46625 0 .empty .empty) .empty)))))))
      (.node 18189392928 771 1 0
        (.node 2015901824 716 1 0
          (.node 1623226368 689 43110 5
            (.node 1088485632 675 46761 0 (.node 1084291520 668 46505 0 (.node 1080097216 665 46559 0 (.node 1080064448 663 46559 0 (.node 1077999872 662 51841 0 .empty .empty) (.node 1080097024 664 46868 0 .empty .empty)) (.node 1082194368 667 51611 0 (.node 1082193984 666 51611 0 .empty .empty) .empty)) (.node 1088452864 672 46761 0 (.node 1086388288 670 51319 0 (.node 1086355904 669 51319 0 .empty .empty) (.node 1086388672 671 51319 0 .empty .empty)) (.node 1088485376 674 46761 0 (.node 1088453056 673 46452 0 .empty .empty) .empty))) (.node 1614838016 682 43110 5 (.node 1346435328 679 25987 0 (.node 1088485760 677 46761 0 (.node 1088485696 676 46452 0 .empty .empty) (.node 1088485824 678 46452 0 .empty .empty)) (.node 1356921088 681 21134 0 (.node 1356920960 680 21134 0 .empty .empty) .empty)) (.node 1614870976 686 42844 5 (.node 1614870528 684 43110 5 (.node 1614838208 683 42844 5 .empty .empty) (.node 1614870784 685 43110 5 .empty .empty)) (.node 1619064832 688 43156 5 (.node 1616935360 687 42844 2 .empty .empty) .empty))))
            (.node 1885370624 703 20976 0 (.node 1625356736 696 42844 2 (.node 1623259584 693 42844 5 (.node 1623259136 691 43110 5 (.node 1623226816 690 42844 5 .empty .empty) (.node 1623259392 692 43110 5 .empty .empty)) (.node 1625356544 695 43109 2 (.node 1625323968 694 42844 2 .empty .empty) .empty)) (.node 1883306240 700 20976 1 (.node 1881208960 698 20976 0 (.node 1881176192 697 20976 0 .empty .empty) (.node 1883273472 699 20976 1 .empty .empty)) (.node 1885370496 702 20976 0 (.node 1883795712 701 1 0 .empty .empty) .empty))) (.node 1893759104 710 20976 0 (.node 1889597696 707 20976 0 (.node 1889564800 705 20976 0 (.node 1885892864 704 1 0 .empty .empty) (.node 1889597568 706 20976 0 .empty .empty)) (.node 1893742848 709 20976 0 (.node 1891694848 708 20976 1 .empty .empty) .empty)) (.node 2015393984 713 11801 0 (.node 1893792000 712 20976 0 (.node 1893791872 711 20976 0 .empty .empty) .empty) (.node 2015901760 715 1 0 (.node 2015899776 714 1 0 .empty .empty) .empty)))))
          (.node 9060105232 744 20317 0
            (.node 8791669776 730 38824 3 (.node 8657452048 723 39170 0 (.node 8590867984 720 42155 0 (.node 2019588288 718 11801 0 (.node 2016163904 717 1 0 .empty .empty) (.node 2020110464 719 1 0 .empty .empty)) (.node 8657321488 722 39170 0 (.node 8657320976 721 39170 0 .empty .empty) .empty)) (.node 8657976848 727 39166 0 (.node 8657845264 725 39166 0 (.node 8657452560 724 39170 0 .empty .empty) (.node 8657845776 726 39166 0 .empty .empty)) (.node 8791538704 729 38824 3 (.node 8724690976 728 38965 3 .empty .empty) .empty))) (.node 8925756944 737 20399 0 (.node 8792194576 734 38823 3 (.node 8791799840 732 38823 3 (.node 8791670288 731 38824 3 .empty .empty) (.node 8792062992 733 38823 3 .empty .empty)) (.node 8925756432 736 20399 0 (.node 8794160208 735 17271 0 .empty .empty) .empty)) (.node 8993388576 741 20334 0 (.node 8926412304 739 20398 0 (.node 8925887504 738 20399 0 .empty .empty) (.node 8993126432 740 20334 0 .empty .empty)) (.node 9059974160 743 20317 0 (.node 8993521184 742 20334 0 .empty .empty) .empty))))
            (.node 9062587408 758 1 0 (.node 9060498464 751 20317 0 (.node 9060367392 748 20317 0 (.node 9060236320 746 20317 0 (.node 9060105744 745 20317 0 .empty .empty) (.node 9060236832 747 20317 0 .empty .empty)) (.node 9060498448 750 20317 0 (.node 9060367904 749 20317 0 .empty .empty) .empty)) (.node 9060630032 755 20317 0 (.node 9060629520 753 20317 0 (.node 9060498976 752 20317 0 .empty .empty) (.node 9060629536 754 20317 0 .empty .empty)) (.node 9062063120 757 1 0 (.node 9060630048 756 20317 0 .empty .empty) .empty))) (.node 17650433056 765 19361 0 (.node 9599458336 762 1 0 (.node 9532086304 760 1 0 (.node 9261561952 759 20320 0 .empty .empty) (.node 9599195168 761 1 0 .empty .empty)) (.node 17381866528 764 27873 3 (.node 9601300512 763 1 0 .empty .empty) .empty)) (.node 18122027136 768 1 0 (.node 18122020896 767 1 0 (.node 17652522016 766 1 0 .empty .empty) .empty) (.node 18189129760 770 1 0 (.node 18187304032 769 11535 0 .empty .empty) .empty))))))
        (.node 35974609152 826 38824 5
          (.node 26508802144 799 11536 0
            (.node 25971669024 785 27675 3 (.node 19199457472 778 11535 0 (.node 18800998528 775 27873 2 (.node 18193324064 773 1 0 (.node 18191235104 772 1 0 .empty .empty) (.node 18193332256 774 1 0 .empty .empty)) (.node 19065761920 777 1 0 (.node 19065239680 776 19361 0 .empty .empty) .empty)) (.node 25904692256 782 27675 3 (.node 25904560160 780 27675 3 (.node 19199979648 779 1 0 .empty .empty) (.node 25904561184 781 27675 3 .empty .empty)) (.node 25906657312 784 8222 0 (.node 25904822304 783 27675 3 .empty .empty) .empty))) (.node 26240366624 792 19262 0 (.node 26172995616 789 19262 0 (.node 25971931168 787 27675 3 (.node 25971801120 786 27675 3 .empty .empty) (.node 25971932192 788 27675 3 .empty .empty)) (.node 26240104480 791 19262 0 (.node 26175084576 790 1 0 .empty .empty) .empty)) (.node 26441431136 796 11536 0 (.node 26240498720 794 19262 0 (.node 26240367648 793 19262 0 .empty .empty) (.node 26242193440 795 1 0 .empty .empty)) (.node 26443520032 798 1 0 (.node 26441432160 797 11536 0 .empty .empty) .empty))))
            (.node 35032955072 813 20320 0 (.node 26779327520 806 1 0 (.node 26777238624 803 11535 0 (.node 26711955488 801 1 0 (.node 26709866592 800 11535 0 .empty .empty) (.node 26777237600 802 11535 0 .empty .empty)) (.node 26779072544 805 1 0 (.node 26779064352 804 1 0 .empty .empty) .empty)) (.node 34374482176 810 42155 0 (.node 26783258656 808 1 0 (.node 26781169696 807 1 0 .empty .empty) (.node 26783266848 809 1 0 .empty .empty)) (.node 34898737280 812 38965 2 (.node 34898720896 811 38965 2 .empty .empty) .empty))) (.node 35446126848 820 39170 1 (.node 35301896320 817 1 0 (.node 35171367040 815 20334 0 (.node 35167172736 814 20334 0 .empty .empty) (.node 35179788416 816 20334 0 .empty .empty)) (.node 35439835392 819 39166 0 (.node 35437738240 818 39170 1 .empty .empty) .empty)) (.node 35714562304 823 20399 1 (.node 35706173696 822 20399 1 (.node 35448224000 821 39166 0 .empty .empty) .empty) (.node 35972479104 825 38823 2 (.node 35716659456 824 20398 0 .empty .empty) .empty)))))
          (.node 36375902336 854 1 0
            (.node 36245141760 840 20317 0 (.node 36240914560 833 20317 0 (.node 35982997760 830 38824 5 (.node 35976706304 828 38823 2 (.node 35976673536 827 38823 2 .empty .empty) (.node 35977197888 829 17271 0 .empty .empty)) (.node 36240898176 832 20317 0 (.node 35985094912 831 38823 2 .empty .empty) .empty)) (.node 36245108864 837 20317 0 (.node 36243044608 835 20317 1 (.node 36240947328 834 20317 0 .empty .empty) (.node 36243534080 836 1 0 .empty .empty)) (.node 36245141632 839 20317 0 (.node 36245108992 838 20317 0 .empty .empty) .empty))) (.node 36253530240 847 20317 0 (.node 36251433216 844 20317 1 (.node 36249303168 842 20317 0 (.node 36245631232 841 1 0 .empty .empty) (.node 36249335936 843 20317 0 .empty .empty)) (.node 36253497600 846 20317 0 (.node 36253497472 845 20317 0 .empty .empty) .empty)) (.node 36375638144 851 1 0 (.node 36375115968 849 11801 0 (.node 36253530368 848 20317 0 .empty .empty) (.node 36375378048 850 1 0 .empty .empty)) (.node 36375900288 853 1 0 (.node 36375640192 852 1 0 .empty .empty) .empty))))
            (.node 53160736896 868 27675 2 (.node 52213330048 861 1 0 (.node 52082800768 858 27675 2 (.node 52078606464 856 27675 2 (.node 36379848832 855 1 0 .empty .empty) (.node 52079114368 857 8222 0 .empty .empty)) (.node 52212824256 860 11536 0 (.node 52086995072 859 27675 2 .empty .empty) .empty)) (.node 52481765504 865 1 0 (.node 52347547776 863 1 0 (.node 52347041920 862 19262 0 .empty .empty) (.node 52481259712 864 11535 0 .empty .empty)) (.node 53156542592 867 27675 2 (.node 53152348288 866 27675 2 .empty .empty) .empty))) (.node 53555507328 875 1 0 (.node 53424978048 872 19262 0 (.node 53420783744 870 19262 0 (.node 53290760384 869 11536 0 .empty .empty) (.node 53421289600 871 1 0 .empty .empty)) (.node 53555247232 874 1 0 (.node 53433366656 873 19262 0 .empty .empty) .empty)) (.node 53555771520 878 1 0 (.node 53555769472 877 1 0 (.node 53555509376 876 1 0 .empty .empty) .empty) (.node 53559718016 880 1 0 (.node 53559195840 879 11535 0 .empty .empty) .empty)))))))))

private def lookup (code : ℕ) : Option (Fin 881) := lookupTree.find code

private def row (i : Fin 881) : ℕ × ℕ × ℕ := lookupTree.getRow i.val

private def pointList : List Point := [
  (-4,0), (-3,-1), (-3,0), (-3,1), (-2,-2), (-2,-1), (-2,0), (-2,1), (-2,2),
  (-1,-3), (-1,-2), (-1,-1), (-1,0), (-1,1), (-1,2), (-1,3),
  (0,-4), (0,-3), (0,-2), (0,-1), (0,0), (0,1), (0,2), (0,3), (0,4),
  (1,-3), (1,-2), (1,-1), (1,0), (1,1), (1,2), (1,3),
  (2,-2), (2,-1), (2,0), (2,1), (2,2), (3,-1), (3,0), (3,1), (4,0)]

private def point (k : Fin 41) : Point := pointList[k.val]!

/-- Actual blocked grid vertices, not an arbitrary finite-state label. -/
def radiusFourMask (i : Fin 881) : Finset Point :=
  (Finset.univ.filter fun k : Fin 41 => (row i).1.testBit k.val).image point

/-- An explicit local order for each represented mask. -/
def radiusFourChoice (i : Fin 881) : Fin 6 :=
  ⟨(row i).2.2 % 6, Nat.mod_lt _ (by decide)⟩

private def encode (F : Finset Point) : ℕ :=
  ∑ k : Fin 41, if point k ∈ F then 2 ^ k.val else 0

/-- Compute the selected controller's successor from actual grid geometry.
The unused action argument matches the shared counting interface. Only the
selected action is claimed; the finite closure theorem excludes lookup failure. -/
def radiusFourStep (i : Fin 881) (_a : Fin 6) (d : Fin 3) : Option (Fin 881) :=
  if direction d ∈ radiusFourMask i then none
  else lookup (encode (memoryStep 4 (radiusFourMask i) (radiusFourChoice i) d))

/-- Original integer weight payload, retained for API compatibility. -/
def radiusFourWeight (i : Fin 881) : ℕ := (row i).2.1

private instance geometry_step_decidable (i : Fin 881) (d : Fin 3) :
    Decidable (match radiusFourStep i (radiusFourChoice i) d with
    | none => direction d ∈ radiusFourMask i
    | some j => direction d ∉ radiusFourMask i ∧
        radiusFourMask j = memoryStep 4 (radiusFourMask i) (radiusFourChoice i) d) := by
  cases radiusFourStep i (radiusFourChoice i) d <;> infer_instance

-- Split the finite quantifier before deciding: each leaf is checked by the kernel
-- in its own auxiliary theorem, without elaborating 881 simultaneous goals.
local syntax "decide_each" num : tactic
local macro_rules
  | `(tactic| decide_each $n:num) => do
    let k := n.getNat
    if k ≤ 1 then
      `(tactic| first
        | (intro i d; fin_cases i; fin_cases d <;> decide +kernel)
        | decide +kernel)
    else
      let a := Lean.Syntax.mkNumLit (toString (k / 2))
      let b := Lean.Syntax.mkNumLit (toString (k - k / 2))
      `(tactic| exact (Fin.forall_fin_add (m := $a:num) (n := $b:num) _).mpr
          ⟨by decide_each $a, by decide_each $b⟩)

/-- Complete selected-controller closure on the actual geometry. The finite
lookup is not allowed to omit an unblocked geometric successor. -/
theorem radiusFour_geometry :
    radiusFourRows.length = 881 ∧
    (radiusFourRows.map fun r => r.1).Nodup ∧
    radiusFourMask 0 = {(-1, 0)} ∧
    (∀ i : Fin 881, (row i).1 < 2199023255552 ∧ (row i).2.2 < 6 ∧ (-1, 0) ∈ radiusFourMask i ∧
      (0, 0) ∉ radiusFourMask i) ∧
    (∀ (i : Fin 881) (d : Fin 3),
      match radiusFourStep i (radiusFourChoice i) d with
      | none => direction d ∈ radiusFourMask i
      | some j => direction d ∉ radiusFourMask i ∧
          radiusFourMask j = memoryStep 4 (radiusFourMask i) (radiusFourChoice i) d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · have h : List.IsChain (· < ·) (radiusFourRows.map fun r => r.1) := by
      decide +kernel
    exact (List.isChain_iff_pairwise.mp h).imp (fun hlt => Nat.ne_of_lt hlt)
  · decide +kernel
  · decide_each 881
  · decide_each 881

/-- All four grid directions at an unconditioned root. -/
def rootDirection (e : Fin 4) : Point :=
  if e = 0 then (1, 0) else if e = 1 then (0, -1)
  else if e = 2 then (0, 1) else (-1, 0)

private def rootRecenter (e : Fin 4) (p : Point) : Point :=
  if e = 0 then (p.1 - 1, p.2) else if e = 1 then (-p.2 - 1, p.1)
  else if e = 2 then (p.2 - 1, -p.1) else (-p.1 - 1, -p.2)

private def rootDeleted (e : Fin 4) : Finset Point :=
  insert (0, 0) ((Finset.univ.filter fun j : Fin 4 => j < e).image rootDirection)

/-- The actual root branch after earlier neighbors and the root are deleted. -/
def rootDomain (V : Finset Point) (e : Fin 4) : Finset Point :=
  (V \ rootDeleted e).image (rootRecenter e)

/-- Four-neighbor root with actual domain-membership tests. An absent root
contributes zero. Nonroot branches use the certified radius-four controller. -/
def rootCount : ℕ → Finset Point → ℕ
  | 0, V => if (0, 0) ∈ V then 1 else 0
  | n + 1, V => if (0, 0) ∈ V then
      ∑ e : Fin 4, if rootDirection e ∈ V then
        orderedCount radiusFourStep radiusFourChoice 0 n (rootDomain V e) 0 else 0
      else 0

#print axioms radiusFour_geometry

end D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourCertificates
