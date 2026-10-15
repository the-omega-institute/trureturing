/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixBoundaryProbe2
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixBoundaryProbe2
   mirror-E: none(waiver:actual-global-cover-kernel-probe)
   anchors: []
   utility: none
   digest: A complete eight-coordinate certificate is replayed with its exact original prefix cache and partial event. -/

/- WIP timing probe for the complete EJM refutation, not an independent
delivery or global acceptance. The native extraction observed 2,497 contexts,
624 four-way splits, 903 bound leaves and 970 symmetry leaves. None of those
counts or native checks is a mathematical premise. The small literal tree is
untrusted certificate data. The kernel checks it directly with the original
global symmetry actions and cache transitions, without importing the large
shared-shape table. Its twelve-coordinate prefix is the actual initial cache
followed by twelve original updates. No native cache state is substituted.
The complete suffix is partitioned into 124 independently checked complete
subtrees, each with at most 61 actual nodes, and 41 explicit four-child
combinations. Every cache and partial event at a cut is the actual parent's
step and update. These are computational staging points, not added premises.
The complete 2,497-node input and final receipt are unchanged. This module
remains unverified until canonical make lean exits zero. -/

import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalScoreSymmetry
import D5.S3.Quantum.Entanglement.EJM.EJMCacheState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixBoundaryProbe2
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState

@[noinline] private def pilotPart0 : RawTree :=
  (.node 39 2898 (.node 19 0 (.node 9 160535141640529 (.node 4 970 (.node 2 969 (.node 1 969 (.node 0 3940651284916269 .empty .empty) .empty) (.node 3 3314388682107022 .empty .empty)) (.node 7 552026779117840 (.node 6 971 (.node 5 1374591399192783 .empty .empty) .empty) (.node 8 972 .empty .empty))) (.node 14 57185881123315 (.node 12 114365854214578 (.node 11 493 (.node 10 493 .empty .empty) .empty) (.node 13 494 .empty .empty)) (.node 17 496 (.node 16 43990668110388 (.node 15 495 .empty .empty) .empty) (.node 18 0 .empty .empty)))) (.node 29 0 (.node 24 0 (.node 22 2898 (.node 21 54988469398228 (.node 20 0 .empty .empty) .empty) (.node 23 0 .empty .empty)) (.node 27 2898 (.node 26 65986270686068 (.node 25 0 .empty .empty) .empty) (.node 28 0 .empty .empty))) (.node 34 2898 (.node 32 79183632231476 (.node 31 103376646532115 (.node 30 0 .empty .empty) .empty) (.node 33 2898 .empty .empty)) (.node 37 90181433519316 (.node 36 0 (.node 35 0 .empty .empty) .empty) (.node 38 2898 .empty .empty))))) (.node 59 2898 (.node 49 2898 (.node 44 2898 (.node 42 101179234807156 (.node 41 0 (.node 40 0 .empty .empty) .empty) (.node 43 2898 .empty .empty)) (.node 47 112177036094996 (.node 46 0 (.node 45 0 .empty .empty) .empty) (.node 48 2898 .empty .empty))) (.node 54 2898 (.node 52 149567411941043 (.node 51 0 (.node 50 0 .empty .empty) .empty) (.node 53 125374397640404 .empty .empty)) (.node 57 0 (.node 56 2898 (.node 55 2898 .empty .empty) .empty) (.node 58 136372198928244 .empty .empty)))) (.node 69 2898 (.node 64 2898 (.node 62 0 (.node 61 2898 (.node 60 2898 .empty .empty) .empty) (.node 63 147370000216084 .empty .empty)) (.node 67 0 (.node 66 2898 (.node 65 2898 .empty .empty) .empty) (.node 68 158367801503924 .empty .empty))) (.node 74 1950 (.node 72 0 (.node 71 2898 (.node 70 2898 .empty .empty) .empty) (.node 73 248539029926226 .empty .empty)) (.node 76 1951 (.node 75 191359056834963 .empty .empty) (.node 77 178163843822036 .empty .empty))))))

@[noinline] private def pilotPart1 : RawTree :=
  (.node 117 2898 (.node 98 224354609230964 (.node 88 2898 (.node 83 2898 (.node 81 0 (.node 80 0 (.node 79 0 .empty .empty) .empty) (.node 82 189161645109876 .empty .empty)) (.node 86 0 (.node 85 0 (.node 84 0 .empty .empty) .empty) (.node 87 200159446397716 .empty .empty))) (.node 93 213356807943124 (.node 91 0 (.node 90 0 (.node 89 0 .empty .empty) .empty) (.node 92 237549822243763 .empty .empty)) (.node 96 0 (.node 95 2898 (.node 94 2898 .empty .empty) .empty) (.node 97 0 .empty .empty)))) (.node 108 246350211806644 (.node 103 235352410518804 (.node 101 0 (.node 100 2898 (.node 99 2898 .empty .empty) .empty) (.node 102 0 .empty .empty)) (.node 106 0 (.node 105 2898 (.node 104 2898 .empty .empty) .empty) (.node 107 0 .empty .empty))) (.node 113 283740587652691 (.node 111 0 (.node 110 2898 (.node 109 2898 .empty .empty) .empty) (.node 112 0 .empty .empty)) (.node 115 2898 (.node 114 259547573352052 .empty .empty) (.node 116 2898 .empty .empty))))) (.node 137 380512645904722 (.node 127 2898 (.node 122 2898 (.node 120 2898 (.node 119 270545374639892 (.node 118 0 .empty .empty) .empty) (.node 121 2898 .empty .empty)) (.node 125 2898 (.node 124 281543175927732 (.node 123 0 .empty .empty) .empty) (.node 126 2898 .empty .empty))) (.node 132 2898 (.node 130 2898 (.node 129 292540977215572 (.node 128 0 .empty .empty) .empty) (.node 131 2898 .empty .empty)) (.node 135 493 (.node 134 426684080814321 (.node 133 0 .empty .empty) .empty) (.node 136 493 .empty .empty)))) (.node 147 332133061851796 (.node 142 496 (.node 140 495 (.node 139 323334820297107 (.node 138 494 .empty .empty) .empty) (.node 141 318935700306388 .empty .empty)) (.node 145 0 (.node 144 0 (.node 143 496 .empty .empty) .empty) (.node 146 0 .empty .empty))) (.node 152 369523437697843 (.node 150 0 (.node 149 0 (.node 148 3374 .empty .empty) .empty) (.node 151 0 .empty .empty)) (.node 154 3374 (.node 153 345330423397204 .empty .empty) (.node 155 3375 .empty .empty))))))

@[noinline] private def pilotPart2 : RawTree :=
  (.node 78 1952 pilotPart0 pilotPart1)

@[noinline] private def pilotPart3 : RawTree :=
  (.node 195 1950 (.node 176 3375 (.node 166 0 (.node 161 0 (.node 159 3374 (.node 158 356328224685044 (.node 157 0 .empty .empty) .empty) (.node 160 0 .empty .empty)) (.node 164 3374 (.node 163 367326025972884 (.node 162 0 .empty .empty) .empty) (.node 165 0 .empty .empty))) (.node 171 0 (.node 169 3374 (.node 168 378323827260724 (.node 167 0 .empty .empty) .empty) (.node 170 0 .empty .empty)) (.node 174 391521188806132 (.node 173 415714203106771 (.node 172 0 .empty .empty) .empty) (.node 175 3374 .empty .empty)))) (.node 186 0 (.node 181 0 (.node 179 402518990093972 (.node 178 0 (.node 177 0 .empty .empty) .empty) (.node 180 3374 .empty .empty)) (.node 184 413516791381812 (.node 183 0 (.node 182 0 .empty .empty) .empty) (.node 185 3374 .empty .empty))) (.node 191 0 (.node 189 424514592669652 (.node 188 0 (.node 187 0 .empty .empty) .empty) (.node 190 3374 .empty .empty)) (.node 193 0 (.node 192 0 .empty .empty) (.node 194 505887580586098 .empty .empty))))) (.node 215 481703159366420 (.node 205 4830 (.node 200 0 (.node 198 444310634987764 (.node 197 1951 (.node 196 448709754978483 .empty .empty) .empty) (.node 199 1952 .empty .empty)) (.node 203 0 (.node 202 0 (.node 201 0 .empty .empty) .empty) (.node 204 457507996533172 .empty .empty))) (.node 210 470705358078580 (.node 208 0 (.node 207 0 (.node 206 0 .empty .empty) .empty) (.node 209 494898372379219 .empty .empty)) (.node 213 0 (.node 212 4831 (.node 211 4830 .empty .empty) .empty) (.node 214 0 .empty .empty)))) (.node 225 503698761942100 (.node 220 492700960654260 (.node 218 0 (.node 217 0 (.node 216 4830 .empty .empty) .empty) (.node 219 0 .empty .empty)) (.node 223 0 (.node 222 0 (.node 221 4830 .empty .empty) .empty) (.node 224 0 .empty .empty))) (.node 230 541089137788147 (.node 228 0 (.node 227 0 (.node 226 4830 .empty .empty) .empty) (.node 229 0 .empty .empty)) (.node 232 4830 (.node 231 516896123487508 .empty .empty) (.node 233 4831 .empty .empty))))))

@[noinline] private def pilotPart4 : RawTree :=
  (.node 273 635670228863571 (.node 254 646659436546034 (.node 244 0 (.node 239 0 (.node 237 4830 (.node 236 527893924775348 (.node 235 0 .empty .empty) .empty) (.node 238 0 .empty .empty)) (.node 242 4830 (.node 241 538891726063188 (.node 240 0 .empty .empty) .empty) (.node 243 0 .empty .empty))) (.node 249 0 (.node 247 4830 (.node 246 549889527351028 (.node 245 0 .empty .empty) .empty) (.node 248 0 .empty .empty)) (.node 252 493 (.node 251 692828723971985 (.node 250 0 .empty .empty) .empty) (.node 253 493 .empty .empty)))) (.node 264 3374 (.node 259 496 (.node 257 495 (.node 256 589479463454771 (.node 255 494 .empty .empty) .empty) (.node 258 576284250441844 .empty .empty)) (.node 262 0 (.node 261 496 (.node 260 496 .empty .empty) .empty) (.node 263 587282051729684 .empty .empty))) (.node 269 3374 (.node 267 0 (.node 266 0 (.node 265 0 .empty .empty) .empty) (.node 268 598279853017524 .empty .empty)) (.node 271 0 (.node 270 0 .empty .empty) (.node 272 0 .empty .empty))))) (.node 293 0 (.node 283 0 (.node 278 0 (.node 276 3375 (.node 275 3374 (.node 274 611477214562932 .empty .empty) .empty) (.node 277 0 .empty .empty)) (.node 281 3376 (.node 280 3374 (.node 279 622475015850772 .empty .empty) .empty) (.node 282 0 .empty .empty))) (.node 288 0 (.node 286 0 (.node 285 3374 (.node 284 633472817138612 .empty .empty) .empty) (.node 287 0 .empty .empty)) (.node 291 0 (.node 290 3374 (.node 289 644470618426452 .empty .empty) .empty) (.node 292 0 .empty .empty)))) (.node 303 0 (.node 298 0 (.node 296 3374 (.node 295 657667979971860 (.node 294 681860994272499 .empty .empty) .empty) (.node 297 3375 .empty .empty)) (.node 301 3374 (.node 300 668665781259700 (.node 299 0 .empty .empty) .empty) (.node 302 0 .empty .empty))) (.node 308 0 (.node 306 3374 (.node 305 679663582547540 (.node 304 0 .empty .empty) .empty) (.node 307 0 .empty .empty)) (.node 310 690661383835380 (.node 309 0 .empty .empty) (.node 311 3374 .empty .empty))))))

@[noinline] private def pilotPart5 : RawTree :=
  (.node 234 0 pilotPart3 pilotPart4)

@[noinline] private def pilotPart6 : RawTree :=
  (.node 156 0 pilotPart2 pilotPart5)

@[noinline] private def pilotPart7 : RawTree :=
  (.node 351 4830 (.node 332 0 (.node 322 0 (.node 317 723652639166419 (.node 315 780832612257682 (.node 314 0 (.node 313 0 .empty .empty) .empty) (.node 316 1950 .empty .empty)) (.node 320 1952 (.node 319 710457426153492 (.node 318 1951 .empty .empty) .empty) (.node 321 0 .empty .empty))) (.node 327 0 (.node 325 4830 (.node 324 721455227441332 (.node 323 0 .empty .empty) .empty) (.node 326 0 .empty .empty)) (.node 330 4830 (.node 329 732453028729172 (.node 328 0 .empty .empty) .empty) (.node 331 0 .empty .empty)))) (.node 342 0 (.node 337 4831 (.node 335 745650390274580 (.node 334 769843404575219 (.node 333 0 .empty .empty) .empty) (.node 336 4830 .empty .empty)) (.node 340 756648191562420 (.node 339 0 (.node 338 0 .empty .empty) .empty) (.node 341 4830 .empty .empty))) (.node 347 0 (.node 345 767645992850260 (.node 344 0 (.node 343 0 .empty .empty) .empty) (.node 346 4830 .empty .empty)) (.node 349 0 (.node 348 0 .empty .empty) (.node 350 778643794138100 .empty .empty))))) (.node 371 824834559547028 (.node 361 802838956971348 (.node 356 791841155683508 (.node 354 0 (.node 353 0 (.node 352 0 .empty .empty) .empty) (.node 355 816034169984147 .empty .empty)) (.node 359 0 (.node 358 4831 (.node 357 4830 .empty .empty) .empty) (.node 360 0 .empty .empty))) (.node 366 813836758259188 (.node 364 0 (.node 363 0 (.node 362 4830 .empty .empty) .empty) (.node 365 0 .empty .empty)) (.node 369 0 (.node 368 0 (.node 367 4830 .empty .empty) .empty) (.node 370 0 .empty .empty)))) (.node 381 873222736156626 (.node 376 1161324309878576 (.node 374 0 (.node 373 0 (.node 372 4830 .empty .empty) .empty) (.node 375 0 .empty .empty)) (.node 379 493 (.node 378 893008039483249 (.node 377 2894 .empty .empty) .empty) (.node 380 493 .empty .empty))) (.node 386 857827963410548 (.node 384 495 (.node 383 860025375660051 (.node 382 494 .empty .empty) .empty) (.node 385 495 .empty .empty)) (.node 388 0 (.node 387 496 .empty .empty) (.node 389 0 .empty .empty))))))

@[noinline] private def pilotPart8 : RawTree :=
  (.node 429 0 (.node 410 910617409592180 (.node 400 888621807016500 (.node 395 0 (.node 393 0 (.node 392 871025324955955 (.node 391 0 .empty .empty) .empty) (.node 394 0 .empty .empty)) (.node 398 0 (.node 397 890819219266003 (.node 396 0 .empty .empty) .empty) (.node 399 0 .empty .empty))) (.node 405 0 (.node 403 2898 (.node 402 2898 (.node 401 2898 .empty .empty) .empty) (.node 404 0 .empty .empty)) (.node 408 923812622605107 (.node 407 1950 (.node 406 945808223607538 .empty .empty) .empty) (.node 409 1951 .empty .empty)))) (.node 420 932613012167860 (.node 415 921615210880020 (.node 413 0 (.node 412 0 (.node 411 1952 .empty .empty) .empty) (.node 414 0 .empty .empty)) (.node 418 0 (.node 417 0 (.node 416 2898 .empty .empty) .empty) (.node 419 0 .empty .empty))) (.node 425 943610813455699 (.node 423 0 (.node 422 0 (.node 421 2898 .empty .empty) .empty) (.node 424 0 .empty .empty)) (.node 427 0 (.node 426 0 .empty .empty) (.node 428 0 .empty .empty))))) (.node 449 493 (.node 439 2898 (.node 434 2898 (.node 432 959007735258676 (.node 431 0 (.node 430 972202948271603 .empty .empty) .empty) (.node 433 2898 .empty .empty)) (.node 437 970005536546516 (.node 436 0 (.node 435 2898 .empty .empty) .empty) (.node 438 2898 .empty .empty))) (.node 444 2898 (.node 442 981003337834356 (.node 441 0 (.node 440 2898 .empty .empty) .empty) (.node 443 2898 .empty .empty)) (.node 447 1071165976322065 (.node 446 0 (.node 445 2898 .empty .empty) .empty) (.node 448 493 .empty .empty)))) (.node 459 0 (.node 454 495 (.node 452 1011795033432243 (.node 451 494 (.node 450 1033790634434674 .empty .empty) .empty) (.node 453 495 .empty .empty)) (.node 457 496 (.node 456 496 (.node 455 1009597621182740 .empty .empty) .empty) (.node 458 0 .empty .empty))) (.node 464 0 (.node 462 0 (.node 461 3374 (.node 460 1020595422470580 .empty .empty) .empty) (.node 463 0 .empty .empty)) (.node 466 0 (.node 465 1031593223758419 .empty .empty) (.node 467 0 .empty .empty))))))

@[noinline] private def pilotPart9 : RawTree :=
  (.node 390 0 pilotPart7 pilotPart8)

@[noinline] private def pilotPart10 : RawTree :=
  (.node 507 0 (.node 488 1950 (.node 478 3375 (.node 473 3375 (.node 471 1044790585303828 (.node 470 1068983599604467 (.node 469 0 .empty .empty) .empty) (.node 472 3374 .empty .empty)) (.node 476 1055788386591668 (.node 475 0 (.node 474 0 .empty .empty) .empty) (.node 477 3374 .empty .empty))) (.node 483 0 (.node 481 1066786187879508 (.node 480 0 (.node 479 0 .empty .empty) .empty) (.node 482 3374 .empty .empty)) (.node 486 0 (.node 485 0 (.node 484 0 .empty .empty) .empty) (.node 487 1123972604470546 .empty .empty)))) (.node 498 0 (.node 493 0 (.node 491 1088781790455188 (.node 490 1951 (.node 489 1101977003468115 .empty .empty) .empty) (.node 492 1952 .empty .empty)) (.node 496 1099779591743028 (.node 495 0 (.node 494 0 .empty .empty) .empty) (.node 497 4830 .empty .empty))) (.node 503 0 (.node 501 1110777393030868 (.node 500 0 (.node 499 0 .empty .empty) .empty) (.node 502 4830 .empty .empty)) (.node 505 0 (.node 504 0 .empty .empty) (.node 506 1121775194318707 .empty .empty))))) (.node 527 0 (.node 517 1145970357151956 (.node 512 1134972555864116 (.node 510 0 (.node 509 0 (.node 508 0 .empty .empty) .empty) (.node 511 1159165570164755 .empty .empty)) (.node 515 0 (.node 514 4831 (.node 513 4830 .empty .empty) .empty) (.node 516 0 .empty .empty))) (.node 522 1156968158439796 (.node 520 0 (.node 519 0 (.node 518 4830 .empty .empty) .empty) (.node 521 0 .empty .empty)) (.node 525 0 (.node 524 0 (.node 523 4830 .empty .empty) .empty) (.node 526 0 .empty .empty)))) (.node 537 496 (.node 532 494 (.node 530 493 (.node 529 493 (.node 528 1258126450207281 .empty .empty) .empty) (.node 531 1211955015297682 .empty .empty)) (.node 535 495 (.node 534 495 (.node 533 1189959414295251 .empty .empty) .empty) (.node 536 1187762002045748 .empty .empty))) (.node 542 3374 (.node 540 0 (.node 539 496 (.node 538 496 .empty .empty) .empty) (.node 541 1198759803333588 .empty .empty)) (.node 544 0 (.node 543 0 .empty .empty) (.node 545 0 .empty .empty))))))

@[noinline] private def pilotPart11 : RawTree :=
  (.node 585 0 (.node 566 0 (.node 556 0 (.node 551 1247147980467475 (.node 549 0 (.node 548 0 (.node 547 0 .empty .empty) .empty) (.node 550 0 .empty .empty)) (.node 554 3375 (.node 553 3374 (.node 552 1222954966166836 .empty .empty) .empty) (.node 555 0 .empty .empty))) (.node 561 0 (.node 559 3375 (.node 558 3374 (.node 557 1233952767454676 .empty .empty) .empty) (.node 560 0 .empty .empty)) (.node 564 0 (.node 563 3374 (.node 562 1244950568742516 .empty .empty) .empty) (.node 565 0 .empty .empty)))) (.node 576 1275744412348468 (.node 571 0 (.node 569 0 (.node 568 3374 (.node 567 1255948370030356 .empty .empty) .empty) (.node 570 0 .empty .empty)) (.node 574 1288939625361395 (.node 573 1950 (.node 572 1328527412408242 .empty .empty) .empty) (.node 575 1951 .empty .empty))) (.node 581 1286742213636308 (.node 579 0 (.node 578 0 (.node 577 1952 .empty .empty) .empty) (.node 580 0 .empty .empty)) (.node 583 0 (.node 582 4830 .empty .empty) (.node 584 0 .empty .empty))))) (.node 605 1339531659817940 (.node 595 0 (.node 590 0 (.node 588 0 (.node 587 4830 (.node 586 1297740014924148 .empty .empty) .empty) (.node 589 0 .empty .empty)) (.node 593 1313136936727124 (.node 592 0 (.node 591 1317536056717843 .empty .empty) .empty) (.node 594 4830 .empty .empty))) (.node 600 4830 (.node 598 0 (.node 597 0 (.node 596 0 .empty .empty) .empty) (.node 599 1326334298272532 .empty .empty)) (.node 603 0 (.node 602 0 (.node 601 0 .empty .empty) .empty) (.node 604 1363724674118579 .empty .empty)))) (.node 615 1361527262393620 (.node 610 1350529461105780 (.node 608 0 (.node 607 4831 (.node 606 4830 .empty .empty) .empty) (.node 609 0 .empty .empty)) (.node 613 0 (.node 612 0 (.node 611 4830 .empty .empty) .empty) (.node 614 0 .empty .empty))) (.node 620 1372525063681460 (.node 618 0 (.node 617 0 (.node 616 4830 .empty .empty) .empty) (.node 619 0 .empty .empty)) (.node 622 0 (.node 621 4830 .empty .empty) (.node 623 0 .empty .empty))))))

@[noinline] private def pilotPart12 : RawTree :=
  (.node 546 1209757604621427 pilotPart10 pilotPart11)

@[noinline] private def pilotPart13 : RawTree :=
  (.node 468 0 pilotPart9 pilotPart12)

@[noinline] private def pilotPart14 : RawTree :=
  (.node 312 0 pilotPart6 pilotPart13)

@[noinline] private def pilotPart15 : RawTree :=
  (.node 663 1467106154756884 (.node 644 0 (.node 634 495 (.node 629 493 (.node 627 1449494636639889 (.node 626 2894 (.node 625 1717808759551568 .empty .empty) .empty) (.node 628 493 .empty .empty)) (.node 632 1398919786772275 (.node 631 494 (.node 630 1420911092807410 .empty .empty) .empty) (.node 633 495 .empty .empty))) (.node 639 0 (.node 637 1418713681082323 (.node 636 0 (.node 635 495 .empty .empty) .empty) (.node 638 0 .empty .empty)) (.node 642 2898 (.node 641 2898 (.node 640 1416516268832820 .empty .empty) .empty) (.node 643 0 .empty .empty)))) (.node 654 2898 (.node 649 2898 (.node 647 0 (.node 646 1447307963906291 (.node 645 0 .empty .empty) .empty) (.node 648 1434112750893364 .empty .empty)) (.node 652 0 (.node 651 2898 (.node 650 2898 .empty .empty) .empty) (.node 653 1445110552181204 .empty .empty))) (.node 659 1493498728266386 (.node 657 0 (.node 656 2898 (.node 655 2898 .empty .empty) .empty) (.node 658 0 .empty .empty)) (.node 661 1471505274747603 (.node 660 1950 .empty .empty) (.node 662 1951 .empty .empty))))) (.node 683 2898 (.node 673 0 (.node 668 0 (.node 666 0 (.node 665 0 (.node 664 1952 .empty .empty) .empty) (.node 667 0 .empty .empty)) (.node 671 0 (.node 670 2898 (.node 669 1480303516302292 .empty .empty) .empty) (.node 672 0 .empty .empty))) (.node 678 0 (.node 676 0 (.node 675 0 (.node 674 1491301317590131 .empty .empty) .empty) (.node 677 0 .empty .empty)) (.node 681 0 (.node 680 0 (.node 679 1511095211900179 .empty .empty) .empty) (.node 682 1508897799650676 .empty .empty)))) (.node 693 493 (.node 688 2898 (.node 686 0 (.node 685 2898 (.node 684 2898 .empty .empty) .empty) (.node 687 1519895600938516 .empty .empty)) (.node 691 0 (.node 690 2898 (.node 689 2898 .empty .empty) .empty) (.node 692 1636446518492849 .empty .empty))) (.node 698 495 (.node 696 494 (.node 695 1590272936099602 (.node 694 493 .empty .empty) .empty) (.node 697 1541891203514195 .empty .empty)) (.node 700 495 (.node 699 495 .empty .empty) (.node 701 1550689444544468 .empty .empty))))))

@[noinline] private def pilotPart16 : RawTree :=
  (.node 741 0 (.node 722 0 (.node 712 1574884607377716 (.node 707 1563886806089876 (.node 705 0 (.node 704 0 (.node 703 496 .empty .empty) .empty) (.node 706 1579283727368307 .empty .empty)) (.node 710 0 (.node 709 3375 (.node 708 3374 .empty .empty) .empty) (.node 711 0 .empty .empty))) (.node 717 0 (.node 715 0 (.node 714 3375 (.node 713 3374 .empty .empty) .empty) (.node 716 0 .empty .empty)) (.node 720 0 (.node 719 3374 (.node 718 1588081968923124 .empty .empty) .empty) (.node 721 0 .empty .empty)))) (.node 732 0 (.node 727 0 (.node 725 3374 (.node 724 1601279330468532 (.node 723 1625472344769171 .empty .empty) .empty) (.node 726 3375 .empty .empty)) (.node 730 3374 (.node 729 1612277131756372 (.node 728 0 .empty .empty) .empty) (.node 731 3375 .empty .empty))) (.node 737 0 (.node 735 3374 (.node 734 1623274933044212 (.node 733 0 .empty .empty) .empty) (.node 736 3375 .empty .empty)) (.node 739 1634272734332052 (.node 738 0 .empty .empty) (.node 740 3374 .empty .empty))))) (.node 761 0 (.node 751 0 (.node 746 1658467896640883 (.node 744 1689257443181874 (.node 743 0 (.node 742 0 .empty .empty) .empty) (.node 745 1950 .empty .empty)) (.node 749 1952 (.node 748 1654068776650164 (.node 747 1951 .empty .empty) .empty) (.node 750 0 .empty .empty))) (.node 756 0 (.node 754 1667266138195572 (.node 753 0 (.node 752 0 .empty .empty) .empty) (.node 755 4830 .empty .empty)) (.node 759 1678263939483411 (.node 758 0 (.node 757 0 .empty .empty) .empty) (.node 760 0 .empty .empty)))) (.node 771 4830 (.node 766 0 (.node 764 4830 (.node 763 1687062180513684 (.node 762 0 .empty .empty) .empty) (.node 765 0 .empty .empty)) (.node 769 0 (.node 768 1706858222307379 (.node 767 0 .empty .empty) .empty) (.node 770 1702459102316660 .empty .empty))) (.node 776 1715656463862068 (.node 774 0 (.node 773 0 (.node 772 0 .empty .empty) .empty) (.node 775 0 .empty .empty)) (.node 778 0 (.node 777 4830 .empty .empty) (.node 779 0 .empty .empty))))))

@[noinline] private def pilotPart17 : RawTree :=
  (.node 702 496 pilotPart15 pilotPart16)

@[noinline] private def pilotPart18 : RawTree :=
  (.node 819 0 (.node 800 1794838484601907 (.node 790 1746450307468020 (.node 785 494 (.node 783 493 (.node 782 493 (.node 781 1805819102349777 .empty .empty) .empty) (.node 784 1759645519956530 .empty .empty)) (.node 788 495 (.node 787 495 (.node 786 1737652066437747 .empty .empty) .empty) (.node 789 495 .empty .empty))) (.node 795 1757448108755859 (.node 793 496 (.node 792 496 (.node 791 496 .empty .empty) .empty) (.node 794 0 .empty .empty)) (.node 798 0 (.node 797 0 (.node 796 0 .empty .empty) .empty) (.node 799 0 .empty .empty)))) (.node 810 0 (.node 805 0 (.node 803 3375 (.node 802 3374 (.node 801 1770645470301268 .empty .empty) .empty) (.node 804 0 .empty .empty)) (.node 808 3375 (.node 807 3374 (.node 806 1781643271589108 .empty .empty) .empty) (.node 809 0 .empty .empty))) (.node 815 0 (.node 813 3375 (.node 812 3374 (.node 811 1792641072876948 .empty .empty) .empty) (.node 814 0 .empty .empty)) (.node 817 3374 (.node 816 1803638874164788 .empty .empty) (.node 818 0 .empty .empty))))) (.node 839 0 (.node 829 0 (.node 824 1951 (.node 822 1950 (.node 821 1858625730498258 (.node 820 0 .empty .empty) .empty) (.node 823 1836630129495827 .empty .empty)) (.node 827 0 (.node 826 1952 (.node 825 1823434916482900 .empty .empty) .empty) (.node 828 0 .empty .empty))) (.node 834 0 (.node 832 0 (.node 831 4830 (.node 830 1834432717770740 .empty .empty) .empty) (.node 833 0 .empty .empty)) (.node 837 0 (.node 836 4830 (.node 835 1845430519058580 .empty .empty) .empty) (.node 838 0 .empty .empty)))) (.node 849 0 (.node 844 0 (.node 842 0 (.node 841 0 (.node 840 1856428320346419 .empty .empty) .empty) (.node 843 0 .empty .empty)) (.node 847 4830 (.node 846 1869625681891828 (.node 845 1885022603170259 .empty .empty) .empty) (.node 848 4831 .empty .empty))) (.node 854 0 (.node 852 4830 (.node 851 1880623483179668 (.node 850 0 .empty .empty) .empty) (.node 853 0 .empty .empty)) (.node 856 0 (.node 855 0 .empty .empty) (.node 857 0 .empty .empty))))))

@[noinline] private def pilotPart19 : RawTree :=
  (.node 897 2898 (.node 878 0 (.node 868 1944408582116531 (.node 863 493 (.node 861 2894 (.node 860 2894 (.node 859 2100530104750992 .empty .empty) .empty) (.node 862 1992779576234993 .empty .empty)) (.node 866 494 (.node 865 1955397791896658 (.node 864 493 .empty .empty) .empty) (.node 867 494 .empty .empty))) (.node 873 0 (.node 871 496 (.node 870 496 (.node 869 1920215567815892 .empty .empty) .empty) (.node 872 0 .empty .empty)) (.node 876 2898 (.node 875 2898 (.node 874 1931213369103732 .empty .empty) .empty) (.node 877 0 .empty .empty)))) (.node 888 0 (.node 883 0 (.node 881 2898 (.node 880 2898 (.node 879 1942211170391572 .empty .empty) .empty) (.node 882 0 .empty .empty)) (.node 886 2898 (.node 885 2898 (.node 884 1953208971679412 .empty .empty) .empty) (.node 887 0 .empty .empty))) (.node 893 2898 (.node 891 2898 (.node 890 1966406333224820 (.node 889 1990599347525459 .empty .empty) .empty) (.node 892 2898 .empty .empty)) (.node 895 1977404134512660 (.node 894 0 .empty .empty) (.node 896 2898 .empty .empty))))) (.node 917 2898 (.node 907 1950 (.node 902 2898 (.node 900 1988401935800500 (.node 899 0 (.node 898 2898 .empty .empty) .empty) (.node 901 2898 .empty .empty)) (.node 905 0 (.node 904 0 (.node 903 2898 .empty .empty) .empty) (.node 906 2071974483974514 .empty .empty))) (.node 912 0 (.node 910 2010397538376180 (.node 909 1951 (.node 908 2014796658366899 .empty .empty) .empty) (.node 911 1952 .empty .empty)) (.node 915 0 (.node 914 0 (.node 913 0 .empty .empty) .empty) (.node 916 2023594899921588 .empty .empty)))) (.node 927 2047790062754836 (.node 922 2036792261466996 (.node 920 0 (.node 919 0 (.node 918 0 .empty .empty) .empty) (.node 921 2060985275767635 .empty .empty)) (.node 925 0 (.node 924 2898 (.node 923 2898 .empty .empty) .empty) (.node 926 0 .empty .empty))) (.node 932 2058787864042676 (.node 930 0 (.node 929 2898 (.node 928 2898 .empty .empty) .empty) (.node 931 0 .empty .empty)) (.node 934 2898 (.node 933 2898 .empty .empty) (.node 935 0 .empty .empty))))))

@[noinline] private def pilotPart20 : RawTree :=
  (.node 858 3013311076619119 pilotPart18 pilotPart19)

@[noinline] private def pilotPart21 : RawTree :=
  (.node 780 0 pilotPart17 pilotPart20)

@[noinline] private def pilotPart22 : RawTree :=
  (.node 975 0 (.node 956 493 (.node 946 2898 (.node 941 0 (.node 939 2898 (.node 938 2898 (.node 937 2069785665330516 .empty .empty) .empty) (.node 940 0 .empty .empty)) (.node 944 2898 (.node 943 2082983026875924 (.node 942 2098379948154355 .empty .empty) .empty) (.node 945 2898 .empty .empty))) (.node 951 2898 (.node 949 2898 (.node 948 2093980828163764 (.node 947 0 .empty .empty) .empty) (.node 950 2898 .empty .empty)) (.node 954 0 (.node 953 0 (.node 952 0 .empty .empty) .empty) (.node 955 2206134773211025 .empty .empty)))) (.node 966 0 (.node 961 2148967686070355 (.node 959 494 (.node 958 2159956895850482 (.node 957 493 .empty .empty) .empty) (.node 960 494 .empty .empty)) (.node 964 496 (.node 963 496 (.node 962 2124774671769716 .empty .empty) .empty) (.node 965 496 .empty .empty))) (.node 971 0 (.node 969 3374 (.node 968 3374 (.node 967 2135772473057556 .empty .empty) .empty) (.node 970 0 .empty .empty)) (.node 973 3374 (.node 972 2146770274345396 .empty .empty) (.node 974 3374 .empty .empty))))) (.node 995 3374 (.node 985 3374 (.node 980 0 (.node 978 3374 (.node 977 2157768075633236 (.node 976 0 .empty .empty) .empty) (.node 979 3374 .empty .empty)) (.node 983 2170965437178644 (.node 982 2195158451479283 (.node 981 0 .empty .empty) .empty) (.node 984 3374 .empty .empty))) (.node 990 3374 (.node 988 2181963238466484 (.node 987 0 (.node 986 0 .empty .empty) .empty) (.node 989 3374 .empty .empty)) (.node 993 2192961039754324 (.node 992 0 (.node 991 0 .empty .empty) .empty) (.node 994 3374 .empty .empty)))) (.node 1005 2236950096373203 (.node 1000 3374 (.node 998 2203958841042164 (.node 997 0 (.node 996 0 .empty .empty) .empty) (.node 999 3374 .empty .empty)) (.node 1003 2294130069464466 (.node 1002 0 (.node 1001 0 .empty .empty) .empty) (.node 1004 1950 .empty .empty))) (.node 1010 0 (.node 1008 1952 (.node 1007 2223754883360276 (.node 1006 1951 .empty .empty) .empty) (.node 1009 0 .empty .empty)) (.node 1012 2234752684648116 (.node 1011 0 .empty .empty) (.node 1013 4830 .empty .empty))))))

@[noinline] private def pilotPart23 : RawTree :=
  (.node 1053 0 (.node 1034 4830 (.node 1024 4830 (.node 1019 0 (.node 1017 2245750485935956 (.node 1016 0 (.node 1015 0 .empty .empty) .empty) (.node 1018 4830 .empty .empty)) (.node 1022 2283140861782003 (.node 1021 0 (.node 1020 0 .empty .empty) .empty) (.node 1023 2258947847481364 .empty .empty))) (.node 1029 4830 (.node 1027 0 (.node 1026 0 (.node 1025 4831 .empty .empty) .empty) (.node 1028 2269945648769204 .empty .empty)) (.node 1032 0 (.node 1031 0 (.node 1030 0 .empty .empty) .empty) (.node 1033 2280943450057044 .empty .empty)))) (.node 1044 2305138612890292 (.node 1039 4830 (.node 1037 0 (.node 1036 0 (.node 1035 0 .empty .empty) .empty) (.node 1038 2291941251344884 .empty .empty)) (.node 1042 0 (.node 1041 0 (.node 1040 0 .empty .empty) .empty) (.node 1043 2329331627190931 .empty .empty))) (.node 1049 2316136414178132 (.node 1047 0 (.node 1046 4831 (.node 1045 4830 .empty .empty) .empty) (.node 1048 0 .empty .empty)) (.node 1051 0 (.node 1050 4830 .empty .empty) (.node 1052 0 .empty .empty))))) (.node 1073 2368925860359763 (.node 1063 0 (.node 1058 0 (.node 1056 0 (.node 1055 4830 (.node 1054 2327134215465972 .empty .empty) .empty) (.node 1057 0 .empty .empty)) (.node 1061 0 (.node 1060 4830 (.node 1059 2338132016753812 .empty .empty) .empty) (.node 1062 0 .empty .empty))) (.node 1068 493 (.node 1066 2894 (.node 1065 2894 (.node 1064 2498663399419184 .empty .empty) .empty) (.node 1067 2399708963925393 .empty .empty)) (.node 1071 494 (.node 1070 2371123272609266 (.node 1069 493 .empty .empty) .empty) (.node 1072 494 .empty .empty)))) (.node 1083 0 (.node 1078 2397520143183603 (.node 1076 0 (.node 1075 0 (.node 1074 495 .empty .empty) .empty) (.node 1077 0 .empty .empty)) (.node 1081 2898 (.node 1080 2898 (.node 1079 2382123221905172 .empty .empty) .empty) (.node 1082 2898 .empty .empty))) (.node 1088 0 (.node 1086 2898 (.node 1085 2898 (.node 1084 2393121023193012 .empty .empty) .empty) (.node 1087 2898 .empty .empty)) (.node 1090 0 (.node 1089 0 .empty .empty) (.node 1091 2470094891118738 .empty .empty))))))

@[noinline] private def pilotPart24 : RawTree :=
  (.node 1014 0 pilotPart22 pilotPart23)

@[noinline] private def pilotPart25 : RawTree :=
  (.node 1131 2898 (.node 1112 0 (.node 1102 2459105682387443 (.node 1097 0 (.node 1095 2417316186026260 (.node 1094 1951 (.node 1093 2421715306016979 .empty .empty) .empty) (.node 1096 1952 .empty .empty)) (.node 1100 0 (.node 1099 0 (.node 1098 0 .empty .empty) .empty) (.node 1101 0 .empty .empty))) (.node 1107 0 (.node 1105 2898 (.node 1104 2898 (.node 1103 2434912668086804 .empty .empty) .empty) (.node 1106 0 .empty .empty)) (.node 1110 2898 (.node 1109 2898 (.node 1108 2445910469374644 .empty .empty) .empty) (.node 1111 0 .empty .empty)))) (.node 1122 0 (.node 1117 0 (.node 1115 2898 (.node 1114 2898 (.node 1113 2456908270662484 .empty .empty) .empty) (.node 1116 0 .empty .empty)) (.node 1120 2898 (.node 1119 2898 (.node 1118 2467906071950324 .empty .empty) .empty) (.node 1121 0 .empty .empty))) (.node 1127 2898 (.node 1125 2898 (.node 1124 2481103433495732 (.node 1123 2496500354774163 .empty .empty) .empty) (.node 1126 2898 .empty .empty)) (.node 1129 2492101234783572 (.node 1128 0 .empty .empty) (.node 1130 2898 .empty .empty))))) (.node 1151 3374 (.node 1141 494 (.node 1136 2569070807742001 (.node 1134 0 (.node 1133 0 (.node 1132 2898 .empty .empty) .empty) (.node 1135 0 .empty .empty)) (.node 1139 2540485116425874 (.node 1138 493 (.node 1137 493 .empty .empty) .empty) (.node 1140 494 .empty .empty))) (.node 1146 496 (.node 1144 2525094638647092 (.node 1143 495 (.node 1142 2529493758637811 .empty .empty) .empty) (.node 1145 496 .empty .empty)) (.node 1149 0 (.node 1148 0 (.node 1147 496 .empty .empty) .empty) (.node 1150 2538292000192500 .empty .empty)))) (.node 1161 2562487163025748 (.node 1156 2551489361737908 (.node 1154 0 (.node 1153 0 (.node 1152 3374 .empty .empty) .empty) (.node 1155 2566886283016339 .empty .empty)) (.node 1159 3375 (.node 1158 3374 (.node 1157 3374 .empty .empty) .empty) (.node 1160 0 .empty .empty))) (.node 1166 0 (.node 1164 0 (.node 1163 3374 (.node 1162 3374 .empty .empty) .empty) (.node 1165 0 .empty .empty)) (.node 1168 2630664937929266 (.node 1167 0 .empty .empty) (.node 1169 1950 .empty .empty))))))

@[noinline] private def pilotPart26 : RawTree :=
  (.node 1209 2835191822810960 (.node 1190 0 (.node 1180 2604278807919540 (.node 1175 0 (.node 1173 1952 (.node 1172 2586682325858996 (.node 1171 1951 .empty .empty) .empty) (.node 1174 0 .empty .empty)) (.node 1178 0 (.node 1177 0 (.node 1176 0 .empty .empty) .empty) (.node 1179 2619675729197971 .empty .empty))) (.node 1185 2615276609207380 (.node 1183 0 (.node 1182 4831 (.node 1181 4830 .empty .empty) .empty) (.node 1184 0 .empty .empty)) (.node 1188 0 (.node 1187 0 (.node 1186 4830 .empty .empty) .empty) (.node 1189 0 .empty .empty)))) (.node 1200 0 (.node 1195 0 (.node 1193 0 (.node 1192 4830 (.node 1191 2628473970752788 .empty .empty) .empty) (.node 1194 0 .empty .empty)) (.node 1198 4830 (.node 1197 2641671332298196 (.node 1196 2657068253576627 .empty .empty) .empty) (.node 1199 4831 .empty .empty))) (.node 1205 0 (.node 1203 4830 (.node 1202 2652669133586036 (.node 1201 0 .empty .empty) .empty) (.node 1204 0 .empty .empty)) (.node 1207 0 (.node 1206 0 .empty .empty) (.node 1208 0 .empty .empty))))) (.node 1229 2898 (.node 1219 495 (.node 1214 493 (.node 1212 2727441294294961 (.node 1211 2894 (.node 1210 2894 .empty .empty) .empty) (.node 1213 493 .empty .empty)) (.node 1217 494 (.node 1216 494 (.node 1215 2698855602978834 .empty .empty) .empty) (.node 1218 2696658190729331 .empty .empty))) (.node 1224 0 (.node 1222 496 (.node 1221 2694460778479828 (.node 1220 495 .empty .empty) .empty) (.node 1223 496 .empty .empty)) (.node 1227 2725254621561235 (.node 1226 0 (.node 1225 0 .empty .empty) .empty) (.node 1228 2709857700282804 .empty .empty)))) (.node 1239 0 (.node 1234 2898 (.node 1232 0 (.node 1231 2898 (.node 1230 2898 .empty .empty) .empty) (.node 1233 2720855501570644 .empty .empty)) (.node 1237 0 (.node 1236 2898 (.node 1235 2898 .empty .empty) .empty) (.node 1238 0 .empty .empty))) (.node 1244 2745050664403892 (.node 1242 2749449784394611 (.node 1241 1950 (.node 1240 2806627610002226 .empty .empty) .empty) (.node 1243 1951 .empty .empty)) (.node 1246 0 (.node 1245 1952 .empty .empty) (.node 1247 0 .empty .empty))))))

@[noinline] private def pilotPart27 : RawTree :=
  (.node 1170 2591081445849715 pilotPart25 pilotPart26)

@[noinline] private def pilotPart28 : RawTree :=
  (.node 1092 1950 pilotPart24 pilotPart27)

@[noinline] private def pilotPart29 : RawTree :=
  (.node 936 0 pilotPart21 pilotPart28)

@[noinline] private def pilotPart30 : RawTree :=
  (.node 624 0 pilotPart14 pilotPart29)

@[noinline] private def pilotPart31 : RawTree :=
  (.node 1288 0 (.node 1268 2898 (.node 1258 2898 (.node 1253 0 (.node 1251 2898 (.node 1250 2758248025949300 (.node 1249 0 .empty .empty) .empty) (.node 1252 0 .empty .empty)) (.node 1256 2771445387494708 (.node 1255 2795638401795347 (.node 1254 0 .empty .empty) .empty) (.node 1257 2898 .empty .empty))) (.node 1263 2898 (.node 1261 2782443188782548 (.node 1260 0 (.node 1259 0 .empty .empty) .empty) (.node 1262 2898 .empty .empty)) (.node 1266 2793440990070388 (.node 1265 0 (.node 1264 0 .empty .empty) .empty) (.node 1267 2898 .empty .empty)))) (.node 1278 2898 (.node 1273 2898 (.node 1271 2804438791358228 (.node 1270 0 (.node 1269 0 .empty .empty) .empty) (.node 1272 2898 .empty .empty)) (.node 1276 2833033074182067 (.node 1275 0 (.node 1274 0 .empty .empty) .empty) (.node 1277 2817636152903636 .empty .empty))) (.node 1283 2898 (.node 1281 0 (.node 1280 2898 (.node 1279 2898 .empty .empty) .empty) (.node 1282 2828633954191476 .empty .empty)) (.node 1286 0 (.node 1285 2898 (.node 1284 2898 .empty .empty) .empty) (.node 1287 0 .empty .empty))))) (.node 1308 2912215095446451 (.node 1298 2863826918312564 (.node 1293 494 (.node 1291 493 (.node 1290 493 (.node 1289 2914399620172113 .empty .empty) .empty) (.node 1292 2877017835833778 .empty .empty)) (.node 1296 495 (.node 1295 2866024330562067 (.node 1294 494 .empty .empty) .empty) (.node 1297 495 .empty .empty))) (.node 1303 2874824719600404 (.node 1301 496 (.node 1300 496 (.node 1299 496 .empty .empty) .empty) (.node 1302 0 .empty .empty)) (.node 1306 0 (.node 1305 3374 (.node 1304 3374 .empty .empty) .empty) (.node 1307 0 .empty .empty)))) (.node 1318 0 (.node 1313 0 (.node 1311 3374 (.node 1310 3374 (.node 1309 2888022081145812 .empty .empty) .empty) (.node 1312 3375 .empty .empty)) (.node 1316 3374 (.node 1315 3374 (.node 1314 2899019882433652 .empty .empty) .empty) (.node 1317 3375 .empty .empty))) (.node 1323 0 (.node 1321 3374 (.node 1320 3374 (.node 1319 2910017683721492 .empty .empty) .empty) (.node 1322 0 .empty .empty)) (.node 1325 2984791991389650 (.node 1324 0 .empty .empty) (.node 1326 1950 .empty .empty))))))

@[noinline] private def pilotPart32 : RawTree :=
  (.node 1366 0 (.node 1347 2971605370933396 (.node 1337 2949609768357716 (.node 1332 0 (.node 1330 1952 (.node 1329 2932013286297172 (.node 1328 1951 .empty .empty) .empty) (.node 1331 0 .empty .empty)) (.node 1335 0 (.node 1334 0 (.node 1333 0 .empty .empty) .empty) (.node 1336 2973802782658355 .empty .empty))) (.node 1342 2960607569645556 (.node 1340 0 (.node 1339 4831 (.node 1338 4830 .empty .empty) .empty) (.node 1341 0 .empty .empty)) (.node 1345 0 (.node 1344 0 (.node 1343 4830 .empty .empty) .empty) (.node 1346 0 .empty .empty)))) (.node 1357 3011197455045075 (.node 1352 2982603172221236 (.node 1350 0 (.node 1349 0 (.node 1348 4830 .empty .empty) .empty) (.node 1351 0 .empty .empty)) (.node 1355 0 (.node 1354 0 (.node 1353 4830 .empty .empty) .empty) (.node 1356 0 .empty .empty))) (.node 1362 0 (.node 1360 4831 (.node 1359 4830 (.node 1358 2995800533766644 .empty .empty) .empty) (.node 1361 0 .empty .empty)) (.node 1364 4830 (.node 1363 3006798335054484 .empty .empty) (.node 1365 0 .empty .empty))))) (.node 1386 0 (.node 1376 3052984804447282 (.node 1371 2894 (.node 1369 0 (.node 1368 0 (.node 1367 0 .empty .empty) .empty) (.node 1370 3162932745212784 .empty .empty)) (.node 1374 493 (.node 1373 3081570495763409 (.node 1372 2894 .empty .empty) .empty) (.node 1375 493 .empty .empty))) (.node 1381 495 (.node 1379 3041991299175571 (.node 1378 494 (.node 1377 494 .empty .empty) .empty) (.node 1380 495 .empty .empty)) (.node 1384 496 (.node 1383 3050789540205844 (.node 1382 495 .empty .empty) .empty) (.node 1385 496 .empty .empty)))) (.node 1396 2898 (.node 1391 2898 (.node 1389 3063986901751252 (.node 1388 3079383823029683 (.node 1387 0 .empty .empty) .empty) (.node 1390 2898 .empty .empty)) (.node 1394 3074984703039092 (.node 1393 0 (.node 1392 2898 .empty .empty) .empty) (.node 1395 2898 .empty .empty))) (.node 1401 3151960718448466 (.node 1399 0 (.node 1398 0 (.node 1397 2898 .empty .empty) .empty) (.node 1400 0 .empty .empty)) (.node 1403 3103578985863059 (.node 1402 1950 .empty .empty) (.node 1404 1951 .empty .empty))))))

@[noinline] private def pilotPart33 : RawTree :=
  (.node 1327 2936412406287891 pilotPart31 pilotPart32)

@[noinline] private def pilotPart34 : RawTree :=
  (.node 1444 3184962715917491 (.node 1425 0 (.node 1415 0 (.node 1410 0 (.node 1408 0 (.node 1407 0 (.node 1406 1952 .empty .empty) .empty) (.node 1409 0 .empty .empty)) (.node 1413 0 (.node 1412 2898 (.node 1411 3112377227417748 .empty .empty) .empty) (.node 1414 0 .empty .empty))) (.node 1420 0 (.node 1418 2898 (.node 1417 3125574588963156 (.node 1416 3140971510241587 .empty .empty) .empty) (.node 1419 2898 .empty .empty)) (.node 1423 2898 (.node 1422 3136572390250996 (.node 1421 0 .empty .empty) .empty) (.node 1424 2898 .empty .empty)))) (.node 1435 0 (.node 1430 2898 (.node 1428 3149769751796404 (.node 1427 0 (.node 1426 0 .empty .empty) .empty) (.node 1429 2898 .empty .empty)) (.node 1433 3160767553084243 (.node 1432 0 (.node 1431 0 .empty .empty) .empty) (.node 1434 0 .empty .empty))) (.node 1440 493 (.node 1438 3224541912505329 (.node 1437 0 (.node 1436 0 .empty .empty) .empty) (.node 1439 493 .empty .empty)) (.node 1442 494 (.node 1441 3195956221189202 .empty .empty) (.node 1443 494 .empty .empty))))) (.node 1464 0 (.node 1454 3206958318493172 (.node 1449 496 (.node 1447 495 (.node 1446 495 (.node 1445 495 .empty .empty) .empty) (.node 1448 3193760956947764 .empty .empty)) (.node 1452 0 (.node 1451 496 (.node 1450 496 .empty .empty) .empty) (.node 1453 3222355239771603 .empty .empty))) (.node 1459 3217956119781012 (.node 1457 3375 (.node 1456 3374 (.node 1455 3374 .empty .empty) .empty) (.node 1458 0 .empty .empty)) (.node 1462 3375 (.node 1461 3374 (.node 1460 3374 .empty .empty) .empty) (.node 1463 0 .empty .empty)))) (.node 1474 0 (.node 1469 1951 (.node 1467 1950 (.node 1466 3286133894684530 (.node 1465 0 .empty .empty) .empty) (.node 1468 3246550402604979 .empty .empty)) (.node 1472 0 (.node 1471 1952 (.node 1470 3242151282614260 .empty .empty) .empty) (.node 1473 0 .empty .empty))) (.node 1479 4830 (.node 1477 3275144685953235 (.node 1476 0 (.node 1475 0 .empty .empty) .empty) (.node 1478 3259747764674804 .empty .empty)) (.node 1481 0 (.node 1480 4831 .empty .empty) (.node 1482 0 .empty .empty))))))

@[noinline] private def pilotPart35 : RawTree :=
  (.node 1522 496 (.node 1503 0 (.node 1493 0 (.node 1488 0 (.node 1486 0 (.node 1485 0 (.node 1484 4830 .empty .empty) .empty) (.node 1487 0 .empty .empty)) (.node 1491 0 (.node 1490 4830 (.node 1489 3283942927508052 .empty .empty) .empty) (.node 1492 0 .empty .empty))) (.node 1498 0 (.node 1496 4830 (.node 1495 3297140289053460 (.node 1494 3312537210331891 .empty .empty) .empty) (.node 1497 4831 .empty .empty)) (.node 1501 4830 (.node 1500 3308138090341300 (.node 1499 0 .empty .empty) .empty) (.node 1502 0 .empty .empty)))) (.node 1513 493 (.node 1508 3325734572401840 (.node 1506 0 (.node 1505 0 (.node 1504 0 .empty .empty) .empty) (.node 1507 3824991782839439 .empty .empty)) (.node 1511 2894 (.node 1510 2894 (.node 1509 2894 .empty .empty) .empty) (.node 1512 3387309371565361 .empty .empty))) (.node 1518 494 (.node 1516 494 (.node 1515 3341131494204818 (.node 1514 493 .empty .empty) .empty) (.node 1517 494 .empty .empty)) (.node 1520 3352129295492660 (.node 1519 3376322309793299 .empty .empty) (.node 1521 496 .empty .empty))))) (.node 1542 3418113954687219 (.node 1532 2898 (.node 1527 2898 (.node 1525 3363127096780500 (.node 1524 0 (.node 1523 496 .empty .empty) .empty) (.node 1526 2898 .empty .empty)) (.node 1530 3374124898068340 (.node 1529 0 (.node 1528 2898 .empty .empty) .empty) (.node 1531 2898 .empty .empty))) (.node 1537 2898 (.node 1535 3385122699356180 (.node 1534 0 (.node 1533 2898 .empty .empty) .empty) (.node 1536 2898 .empty .empty)) (.node 1540 3466495687272626 (.node 1539 0 (.node 1538 2898 .empty .empty) .empty) (.node 1541 1950 .empty .empty)))) (.node 1552 0 (.node 1547 0 (.node 1545 1952 (.node 1544 3404918741674292 (.node 1543 1951 .empty .empty) .empty) (.node 1546 0 .empty .empty)) (.node 1550 2898 (.node 1549 3415916542962132 (.node 1548 0 .empty .empty) .empty) (.node 1551 0 .empty .empty))) (.node 1557 2898 (.node 1555 3455506479065747 (.node 1554 0 (.node 1553 0 .empty .empty) .empty) (.node 1556 3431313464765108 .empty .empty)) (.node 1559 0 (.node 1558 2898 .empty .empty) (.node 1560 0 .empty .empty))))))

@[noinline] private def pilotPart36 : RawTree :=
  (.node 1483 3270745565962644 pilotPart34 pilotPart35)

@[noinline] private def pilotPart37 : RawTree :=
  (.node 1405 3099179865872340 pilotPart33 pilotPart36)

@[noinline] private def pilotPart38 : RawTree :=
  (.node 1600 2894 (.node 1581 0 (.node 1571 3464306868628628 (.node 1566 3453309067340788 (.node 1564 0 (.node 1563 2898 (.node 1562 2898 .empty .empty) .empty) (.node 1565 0 .empty .empty)) (.node 1569 0 (.node 1568 2898 (.node 1567 2898 .empty .empty) .empty) (.node 1570 0 .empty .empty))) (.node 1576 3501697244474675 (.node 1574 0 (.node 1573 2898 (.node 1572 2898 .empty .empty) .empty) (.node 1575 0 .empty .empty)) (.node 1579 2898 (.node 1578 2898 (.node 1577 3477504230174036 .empty .empty) .empty) (.node 1580 2898 .empty .empty)))) (.node 1591 0 (.node 1586 0 (.node 1584 2898 (.node 1583 2898 (.node 1582 3488502031461876 .empty .empty) .empty) (.node 1585 2898 .empty .empty)) (.node 1589 2898 (.node 1588 2898 (.node 1587 3499499832749716 .empty .empty) .empty) (.node 1590 2898 .empty .empty))) (.node 1596 0 (.node 1594 2898 (.node 1593 2898 (.node 1592 3510497634037556 .empty .empty) .empty) (.node 1595 2898 .empty .empty)) (.node 1598 2894 (.node 1597 3521495435325392 .empty .empty) (.node 1599 2894 .empty .empty))))) (.node 1620 3572085321249460 (.node 1610 3550089718673780 (.node 1605 494 (.node 1603 493 (.node 1602 493 (.node 1601 3574274141466705 .empty .empty) .empty) (.node 1604 3536892357128370 .empty .empty)) (.node 1608 3563284931686707 (.node 1607 494 (.node 1606 494 .empty .empty) .empty) (.node 1609 495 .empty .empty))) (.node 1615 3561087519961620 (.node 1613 496 (.node 1612 496 (.node 1611 496 .empty .empty) .empty) (.node 1614 0 .empty .empty)) (.node 1618 2898 (.node 1617 2898 (.node 1616 2898 .empty .empty) .empty) (.node 1619 0 .empty .empty)))) (.node 1630 1952 (.node 1625 3627067882615634 (.node 1623 2898 (.node 1622 2898 (.node 1621 2898 .empty .empty) .empty) (.node 1624 0 .empty .empty)) (.node 1628 1951 (.node 1627 3596280483558291 (.node 1626 1950 .empty .empty) .empty) (.node 1629 3591881363567572 .empty .empty))) (.node 1635 0 (.node 1633 0 (.node 1632 0 (.node 1631 0 .empty .empty) .empty) (.node 1634 0 .empty .empty)) (.node 1637 3609477845628116 (.node 1636 3624874766906547 .empty .empty) (.node 1638 2898 .empty .empty))))))

@[noinline] private def pilotPart39 : RawTree :=
  (.node 1678 2898 (.node 1659 2894 (.node 1649 3644670809224787 (.node 1644 2898 (.node 1642 3620475646915956 (.node 1641 0 (.node 1640 0 .empty .empty) .empty) (.node 1643 2898 .empty .empty)) (.node 1647 0 (.node 1646 0 (.node 1645 0 .empty .empty) .empty) (.node 1648 0 .empty .empty))) (.node 1654 2898 (.node 1652 2898 (.node 1651 3640271689234068 (.node 1650 0 .empty .empty) .empty) (.node 1653 2898 .empty .empty)) (.node 1657 0 (.node 1656 0 (.node 1655 0 .empty .empty) .empty) (.node 1658 3655668611037040 .empty .empty)))) (.node 1669 3688659866892499 (.node 1664 493 (.node 1662 3699651224156145 (.node 1661 2894 (.node 1660 2894 .empty .empty) .empty) (.node 1663 493 .empty .empty)) (.node 1667 494 (.node 1666 494 (.node 1665 3671065532840018 .empty .empty) .empty) (.node 1668 494 .empty .empty))) (.node 1674 496 (.node 1672 3686462454642996 (.node 1671 495 (.node 1670 495 .empty .empty) .empty) (.node 1673 496 .empty .empty)) (.node 1676 0 (.node 1675 496 .empty .empty) (.node 1677 3697460255930836 .empty .empty))))) (.node 1698 3743651021339764 (.node 1688 0 (.node 1683 1950 (.node 1681 0 (.node 1680 2898 (.node 1679 2898 .empty .empty) .empty) (.node 1682 3778833243847282 .empty .empty)) (.node 1686 3717256298248948 (.node 1685 1951 (.node 1684 3730451511261875 .empty .empty) .empty) (.node 1687 1952 .empty .empty))) (.node 1693 0 (.node 1691 3728254099536788 (.node 1690 0 (.node 1689 0 .empty .empty) .empty) (.node 1692 2898 .empty .empty)) (.node 1696 0 (.node 1695 0 (.node 1694 0 .empty .empty) .empty) (.node 1697 3767844035640403 .empty .empty)))) (.node 1708 3765646623915444 (.node 1703 3754648822627604 (.node 1701 0 (.node 1700 2898 (.node 1699 2898 .empty .empty) .empty) (.node 1702 0 .empty .empty)) (.node 1706 0 (.node 1705 2898 (.node 1704 2898 .empty .empty) .empty) (.node 1707 0 .empty .empty))) (.node 1713 3776644425203284 (.node 1711 0 (.node 1710 2898 (.node 1709 2898 .empty .empty) .empty) (.node 1712 0 .empty .empty)) (.node 1715 2898 (.node 1714 2898 .empty .empty) (.node 1716 0 .empty .empty))))))

@[noinline] private def pilotPart40 : RawTree :=
  (.node 1639 2898 pilotPart38 pilotPart39)

@[noinline] private def pilotPart41 : RawTree :=
  (.node 1756 496 (.node 1737 2898 (.node 1727 2898 (.node 1722 2898 (.node 1720 2898 (.node 1719 3789841786748692 (.node 1718 3814034801049331 .empty .empty) .empty) (.node 1721 2898 .empty .empty)) (.node 1725 2898 (.node 1724 3800839588036532 (.node 1723 0 .empty .empty) .empty) (.node 1726 2898 .empty .empty))) (.node 1732 2898 (.node 1730 2898 (.node 1729 3811837389324372 (.node 1728 0 .empty .empty) .empty) (.node 1731 2898 .empty .empty)) (.node 1735 2898 (.node 1734 3822835190612212 (.node 1733 0 .empty .empty) .empty) (.node 1736 2898 .empty .empty)))) (.node 1747 494 (.node 1742 2894 (.node 1740 2894 (.node 1739 3833832991900048 (.node 1738 0 .empty .empty) .empty) (.node 1741 2894 .empty .empty)) (.node 1745 493 (.node 1744 493 (.node 1743 3869019511996945 .empty .empty) .empty) (.node 1746 3849229913703026 .empty .empty))) (.node 1752 495 (.node 1750 3858028154733299 (.node 1749 494 (.node 1748 494 .empty .empty) .empty) (.node 1751 495 .empty .empty)) (.node 1754 3866826395763572 (.node 1753 495 .empty .empty) (.node 1755 496 .empty .empty))))) (.node 1776 3915216721430068 (.node 1766 0 (.node 1761 3891021558072403 (.node 1759 3921808957129746 (.node 1758 0 (.node 1757 496 .empty .empty) .empty) (.node 1760 1950 .empty .empty)) (.node 1764 1952 (.node 1763 3886622438081684 (.node 1762 1951 .empty .empty) .empty) (.node 1765 0 .empty .empty))) (.node 1771 3904218920142228 (.node 1769 0 (.node 1768 0 (.node 1767 0 .empty .empty) .empty) (.node 1770 3919615841420659 .empty .empty)) (.node 1774 0 (.node 1773 2898 (.node 1772 2898 .empty .empty) .empty) (.node 1775 0 .empty .empty)))) (.node 1786 2898 (.node 1781 0 (.node 1779 0 (.node 1778 2898 (.node 1777 2898 .empty .empty) .empty) (.node 1780 0 .empty .empty)) (.node 1784 0 (.node 1783 3939411883738899 (.node 1782 0 .empty .empty) .empty) (.node 1785 3935012763748180 .empty .empty))) (.node 1791 0 (.node 1789 0 (.node 1788 2898 (.node 1787 2898 .empty .empty) .empty) (.node 1790 0 .empty .empty)) (.node 1793 990 (.node 1792 5305203431983150 .empty .empty) (.node 1794 4482634516940911 .empty .empty))))))

@[noinline] private def pilotPart42 : RawTree :=
  (.node 1834 3374 (.node 1815 0 (.node 1805 493 (.node 1800 493 (.node 1798 3963607047096561 (.node 1797 992 (.node 1796 4099947562420400 .empty .empty) .empty) (.node 1799 493 .empty .empty)) (.node 1803 3974604848384401 (.node 1802 997 (.node 1801 493 .empty .empty) .empty) (.node 1804 493 .empty .empty))) (.node 1810 495 (.node 1808 494 (.node 1807 4053778276043282 (.node 1806 493 .empty .empty) .empty) (.node 1809 3996600450435667 .empty .empty)) (.node 1813 496 (.node 1812 496 (.node 1811 3992201330444948 .empty .empty) .empty) (.node 1814 0 .empty .empty)))) (.node 1825 3375 (.node 1820 0 (.node 1818 3374 (.node 1817 4005398691990356 (.node 1816 0 .empty .empty) .empty) (.node 1819 0 .empty .empty)) (.node 1823 4018596053535764 (.node 1822 4042789067836403 (.node 1821 0 .empty .empty) .empty) (.node 1824 3374 .empty .empty))) (.node 1830 0 (.node 1828 4029593854823604 (.node 1827 0 (.node 1826 0 .empty .empty) .empty) (.node 1829 3374 .empty .empty)) (.node 1832 0 (.node 1831 0 .empty .empty) (.node 1833 4040591656111444 .empty .empty))))) (.node 1854 4086782421520372 (.node 1844 4064786818944692 (.node 1839 3374 (.node 1837 0 (.node 1836 0 (.node 1835 0 .empty .empty) .empty) (.node 1838 4051589457399284 .empty .empty)) (.node 1842 0 (.node 1841 0 (.node 1840 0 .empty .empty) .empty) (.node 1843 4088979833245331 .empty .empty))) (.node 1849 4075784620232532 (.node 1847 0 (.node 1846 3375 (.node 1845 3374 .empty .empty) .empty) (.node 1848 0 .empty .empty)) (.node 1852 0 (.node 1851 0 (.node 1850 3374 .empty .empty) .empty) (.node 1853 0 .empty .empty)))) (.node 1864 4108778024096049 (.node 1859 4097780222808212 (.node 1857 0 (.node 1856 0 (.node 1855 3374 .empty .empty) .empty) (.node 1858 0 .empty .empty)) (.node 1862 0 (.node 1861 0 (.node 1860 3374 .empty .empty) .empty) (.node 1863 0 .empty .empty))) (.node 1869 494 (.node 1867 493 (.node 1866 493 (.node 1865 493 .empty .empty) .empty) (.node 1868 4161563172688306 .empty .empty)) (.node 1871 495 (.node 1870 4139569719169523 .empty .empty) (.node 1872 4126374506156596 .empty .empty))))))

@[noinline] private def pilotPart43 : RawTree :=
  (.node 1795 991 pilotPart41 pilotPart42)

@[noinline] private def pilotPart44 : RawTree :=
  (.node 1717 0 pilotPart40 pilotPart43)

@[noinline] private def pilotPart45 : RawTree :=
  (.node 1561 3442311266052948 pilotPart37 pilotPart44)

@[noinline] private def pilotPart46 : RawTree :=
  (.node 1912 493 (.node 1893 4172565271565524 (.node 1883 4159367909495699 (.node 1878 3374 (.node 1876 0 (.node 1875 496 (.node 1874 496 .empty .empty) .empty) (.node 1877 4137372307444436 .empty .empty)) (.node 1881 0 (.node 1880 0 (.node 1879 0 .empty .empty) .empty) (.node 1882 0 .empty .empty))) (.node 1888 0 (.node 1886 3374 (.node 1885 4154968789504980 (.node 1884 0 .empty .empty) .empty) (.node 1887 3376 .empty .empty)) (.node 1891 0 (.node 1890 0 (.node 1889 0 .empty .empty) .empty) (.node 1892 4196758285866163 .empty .empty)))) (.node 1903 4194560874141204 (.node 1898 4183563072853364 (.node 1896 0 (.node 1895 3375 (.node 1894 3374 .empty .empty) .empty) (.node 1897 0 .empty .empty)) (.node 1901 0 (.node 1900 0 (.node 1899 3374 .empty .empty) .empty) (.node 1902 0 .empty .empty))) (.node 1908 0 (.node 1906 0 (.node 1905 0 (.node 1904 3374 .empty .empty) .empty) (.node 1907 0 .empty .empty)) (.node 1910 2894 (.node 1909 4392497663989456 .empty .empty) (.node 1911 4212157356201745 .empty .empty))))) (.node 1932 0 (.node 1922 0 (.node 1917 4234150810769363 (.node 1915 4264942504794002 (.node 1914 493 (.node 1913 493 .empty .empty) .empty) (.node 1916 494 .empty .empty)) (.node 1920 4231953398519860 (.node 1919 495 (.node 1918 495 .empty .empty) .empty) (.node 1921 496 .empty .empty))) (.node 1927 0 (.node 1925 4242951199807700 (.node 1924 0 (.node 1923 0 .empty .empty) .empty) (.node 1926 2898 .empty .empty)) (.node 1930 4253949001095539 (.node 1929 0 (.node 1928 0 .empty .empty) .empty) (.node 1931 0 .empty .empty)))) (.node 1942 4280343724186356 (.node 1937 0 (.node 1935 2898 (.node 1934 4262747242125812 (.node 1933 0 .empty .empty) .empty) (.node 1936 2898 .empty .empty)) (.node 1940 0 (.node 1939 4282541136435859 (.node 1938 0 .empty .empty) .empty) (.node 1941 0 .empty .empty))) (.node 1947 4291341525474196 (.node 1945 2898 (.node 1944 2898 (.node 1943 2898 .empty .empty) .empty) (.node 1946 0 .empty .empty)) (.node 1949 2898 (.node 1948 2898 .empty .empty) (.node 1950 2898 .empty .empty))))))

@[noinline] private def pilotPart47 : RawTree :=
  (.node 1990 0 (.node 1971 4352929212161683 (.node 1961 4322135369080148 (.node 1956 4363920568376498 (.node 1954 493 (.node 1953 493 (.node 1952 4302339326762033 .empty .empty) .empty) (.node 1955 493 .empty .empty)) (.node 1959 495 (.node 1958 4324332781329651 (.node 1957 494 .empty .empty) .empty) (.node 1960 495 .empty .empty))) (.node 1966 4333133170367988 (.node 1964 0 (.node 1963 496 (.node 1962 496 .empty .empty) .empty) (.node 1965 0 .empty .empty)) (.node 1969 0 (.node 1968 0 (.node 1967 3374 .empty .empty) .empty) (.node 1970 0 .empty .empty)))) (.node 1981 0 (.node 1976 0 (.node 1974 3374 (.node 1973 4348530092170964 (.node 1972 0 .empty .empty) .empty) (.node 1975 3375 .empty .empty)) (.node 1979 4361727453716372 (.node 1978 0 (.node 1977 0 .empty .empty) .empty) (.node 1980 3374 .empty .empty))) (.node 1986 3374 (.node 1984 4390319589056563 (.node 1983 0 (.node 1982 0 .empty .empty) .empty) (.node 1985 4374924815261780 .empty .empty)) (.node 1988 0 (.node 1987 3375 .empty .empty) (.node 1989 0 .empty .empty))))) (.node 2010 0 (.node 2000 493 (.node 1995 0 (.node 1993 0 (.node 1992 3374 (.node 1991 4388122176807188 .empty .empty) .empty) (.node 1994 0 .empty .empty)) (.node 1998 493 (.node 1997 4401319538352593 (.node 1996 0 .empty .empty) .empty) (.node 1999 493 .empty .empty))) (.node 2005 495 (.node 2003 4423312992920211 (.node 2002 494 (.node 2001 4445306446438994 .empty .empty) .empty) (.node 2004 495 .empty .empty)) (.node 2008 496 (.node 2007 496 (.node 2006 4421115580670708 .empty .empty) .empty) (.node 2009 496 .empty .empty)))) (.node 2020 0 (.node 2015 3374 (.node 2013 0 (.node 2012 4443111182721971 (.node 2011 0 .empty .empty) .empty) (.node 2014 4438712062731252 .empty .empty)) (.node 2018 0 (.node 2017 0 (.node 2016 3375 .empty .empty) .empty) (.node 2019 0 .empty .empty))) (.node 2025 0 (.node 2023 3374 (.node 2022 4456308544791796 (.node 2021 4480501559092435 .empty .empty) .empty) (.node 2024 3375 .empty .empty)) (.node 2027 4467306346079636 (.node 2026 0 .empty .empty) (.node 2028 3374 .empty .empty))))))

@[noinline] private def pilotPart48 : RawTree :=
  (.node 1951 0 pilotPart46 pilotPart47)

@[noinline] private def pilotPart49 : RawTree :=
  (.node 2068 4566284409662131 (.node 2049 495 (.node 2039 2894 (.node 2034 0 (.node 2032 4478304147367476 (.node 2031 0 (.node 2030 0 .empty .empty) .empty) (.node 2033 3374 .empty .empty)) (.node 2037 0 (.node 2036 0 (.node 2035 0 .empty .empty) .empty) (.node 2038 4685037030237936 .empty .empty))) (.node 2044 4548683630536626 (.node 2042 493 (.node 2041 493 (.node 2040 4495900629428017 .empty .empty) .empty) (.node 2043 493 .empty .empty)) (.node 2047 495 (.node 2046 4509097990973427 (.node 2045 494 .empty .empty) .empty) (.node 2048 495 .empty .empty)))) (.node 2059 2898 (.node 2054 0 (.node 2052 0 (.node 2051 496 (.node 2050 4517896232003700 .empty .empty) .empty) (.node 2053 0 .empty .empty)) (.node 2057 0 (.node 2056 0 (.node 2055 4537690126313747 .empty .empty) .empty) (.node 2058 4535492714064244 .empty .empty))) (.node 2064 2898 (.node 2062 0 (.node 2061 0 (.node 2060 2898 .empty .empty) .empty) (.node 2063 4546490515352084 .empty .empty)) (.node 2066 0 (.node 2065 2898 .empty .empty) (.node 2067 0 .empty .empty))))) (.node 2088 495 (.node 2078 2898 (.node 2073 2898 (.node 2071 4564086997412628 (.node 2070 0 (.node 2069 0 .empty .empty) .empty) (.node 2072 2898 .empty .empty)) (.node 2076 4575084798700468 (.node 2075 0 (.node 2074 2898 .empty .empty) .empty) (.node 2077 2898 .empty .empty))) (.node 2083 493 (.node 2081 4586082599988305 (.node 2080 0 (.node 2079 2898 .empty .empty) .empty) (.node 2082 493 .empty .empty)) (.node 2086 494 (.node 2085 4656457787141330 (.node 2084 493 .empty .empty) .empty) (.node 2087 4599279961533715 .empty .empty)))) (.node 2098 3374 (.node 2093 496 (.node 2091 4608078202563988 (.node 2090 495 (.node 2089 495 .empty .empty) .empty) (.node 2092 496 .empty .empty)) (.node 2096 4645468578410035 (.node 2095 0 (.node 2094 0 .empty .empty) .empty) (.node 2097 4621275564109396 .empty .empty))) (.node 2103 3374 (.node 2101 0 (.node 2100 0 (.node 2099 3375 .empty .empty) .empty) (.node 2102 4632273365397236 .empty .empty)) (.node 2105 0 (.node 2104 3375 .empty .empty) (.node 2106 0 .empty .empty))))))

@[noinline] private def pilotPart50 : RawTree :=
  (.node 2146 0 (.node 2127 0 (.node 2117 4674062862282963 (.node 2112 4654268967972916 (.node 2110 0 (.node 2109 3375 (.node 2108 3374 .empty .empty) .empty) (.node 2111 0 .empty .empty)) (.node 2115 0 (.node 2114 0 (.node 2113 3374 .empty .empty) .empty) (.node 2116 0 .empty .empty))) (.node 2122 3375 (.node 2120 4671865450033460 (.node 2119 0 (.node 2118 0 .empty .empty) .empty) (.node 2121 3374 .empty .empty)) (.node 2125 4682863251321300 (.node 2124 0 (.node 2123 0 .empty .empty) .empty) (.node 2126 3374 .empty .empty)))) (.node 2137 495 (.node 2132 493 (.node 2130 4693861052609137 (.node 2129 0 (.node 2128 0 .empty .empty) .empty) (.node 2131 493 .empty .empty)) (.node 2135 494 (.node 2134 4737847960695538 (.node 2133 493 .empty .empty) .empty) (.node 2136 4707058414154547 .empty .empty))) (.node 2142 496 (.node 2140 4715856655184820 (.node 2139 495 (.node 2138 495 .empty .empty) .empty) (.node 2141 496 .empty .empty)) (.node 2144 0 (.node 2143 496 .empty .empty) (.node 2145 4735652696978515 .empty .empty))))) (.node 2166 493 (.node 2156 0 (.node 2151 0 (.node 2149 3375 (.node 2148 3374 (.node 2147 4731253576987796 .empty .empty) .empty) (.node 2150 0 .empty .empty)) (.node 2154 4746650498790771 (.node 2153 0 (.node 2152 0 .empty .empty) .empty) (.node 2155 0 .empty .empty))) (.node 2161 2894 (.node 2159 5206326365156879 (.node 2158 0 (.node 2157 0 .empty .empty) .empty) (.node 2160 4847808790558256 .empty .empty)) (.node 2164 493 (.node 2163 4766446541108881 (.node 2162 2894 .empty .empty) .empty) (.node 2165 493 .empty .empty)))) (.node 2176 4795040824457268 (.node 2171 4784043023169428 (.node 2169 494 (.node 2168 494 (.node 2167 4819225247250194 .empty .empty) .empty) (.node 2170 4808236037470067 .empty .empty)) (.node 2174 0 (.node 2173 496 (.node 2172 496 .empty .empty) .empty) (.node 2175 0 .empty .empty))) (.node 2181 4806038625745108 (.node 2179 0 (.node 2178 2898 (.node 2177 2898 .empty .empty) .empty) (.node 2180 0 .empty .empty)) (.node 2183 2898 (.node 2182 2898 .empty .empty) (.node 2184 0 .empty .empty))))))

@[noinline] private def pilotPart51 : RawTree :=
  (.node 2107 4643271166685076 pilotPart49 pilotPart50)

@[noinline] private def pilotPart52 : RawTree :=
  (.node 2029 3375 pilotPart48 pilotPart51)

@[noinline] private def pilotPart53 : RawTree :=
  (.node 2224 3374 (.node 2205 493 (.node 2195 2898 (.node 2190 0 (.node 2188 2898 (.node 2187 2898 (.node 2186 4817036427032948 .empty .empty) .empty) (.node 2189 0 .empty .empty)) (.node 2193 2898 (.node 2192 4830233788578356 (.node 2191 4845630709856787 .empty .empty) .empty) (.node 2194 2898 .empty .empty))) (.node 2200 2898 (.node 2198 2898 (.node 2197 4841231589866196 (.node 2196 0 .empty .empty) .empty) (.node 2199 2898 .empty .empty)) (.node 2203 0 (.node 2202 0 (.node 2201 0 .empty .empty) .empty) (.node 2204 4856628511669169 .empty .empty)))) (.node 2215 496 (.node 2210 494 (.node 2208 4909407217810482 (.node 2207 493 (.node 2206 493 .empty .empty) .empty) (.node 2209 494 .empty .empty)) (.node 2213 496 (.node 2212 4874224993729716 (.node 2211 4898418008030355 .empty .empty) .empty) (.node 2214 496 .empty .empty))) (.node 2220 0 (.node 2218 3374 (.node 2217 4885222795017556 (.node 2216 0 .empty .empty) .empty) (.node 2219 3374 .empty .empty)) (.node 2222 4896220596305396 (.node 2221 0 .empty .empty) (.node 2223 3374 .empty .empty))))) (.node 2244 3374 (.node 2234 3374 (.node 2229 3374 (.node 2227 4907218397593236 (.node 2226 0 (.node 2225 0 .empty .empty) .empty) (.node 2228 3374 .empty .empty)) (.node 2232 4944608773439283 (.node 2231 0 (.node 2230 0 .empty .empty) .empty) (.node 2233 4920415759138644 .empty .empty))) (.node 2239 3374 (.node 2237 0 (.node 2236 0 (.node 2235 3374 .empty .empty) .empty) (.node 2238 4931413560426484 .empty .empty)) (.node 2242 0 (.node 2241 0 (.node 2240 3374 .empty .empty) .empty) (.node 2243 4942411361714324 .empty .empty)))) (.node 2254 493 (.node 2249 5025977467437392 (.node 2247 0 (.node 2246 0 (.node 2245 3374 .empty .empty) .empty) (.node 2248 0 .empty .empty)) (.node 2252 4962207404032433 (.node 2251 2894 (.node 2250 2894 .empty .empty) .empty) (.node 2253 493 .empty .empty))) (.node 2259 4995198659363475 (.node 2257 494 (.node 2256 5006190017151538 (.node 2255 493 .empty .empty) .empty) (.node 2258 494 .empty .empty)) (.node 2261 4982003446350548 (.node 2260 495 .empty .empty) (.node 2262 496 .empty .empty))))))

@[noinline] private def pilotPart54 : RawTree :=
  (.node 2302 0 (.node 2283 0 (.node 2273 2898 (.node 2268 2898 (.node 2266 4993001247638388 (.node 2265 0 (.node 2264 0 .empty .empty) .empty) (.node 2267 2898 .empty .empty)) (.node 2271 5003999048926228 (.node 2270 0 (.node 2269 0 .empty .empty) .empty) (.node 2272 2898 .empty .empty))) (.node 2278 2898 (.node 2276 5023795091244211 (.node 2275 0 (.node 2274 0 .empty .empty) .empty) (.node 2277 5017196410471636 .empty .empty)) (.node 2281 0 (.node 2280 2898 (.node 2279 2898 .empty .empty) .empty) (.node 2282 0 .empty .empty)))) (.node 2293 495 (.node 2288 493 (.node 2286 493 (.node 2285 5034792892532177 (.node 2284 0 .empty .empty) .empty) (.node 2287 493 .empty .empty)) (.node 2291 494 (.node 2290 494 (.node 2289 5052387226584658 .empty .empty) .empty) (.node 2292 5050189814335155 .empty .empty))) (.node 2298 5063387175880564 (.node 2296 0 (.node 2295 0 (.node 2294 0 .empty .empty) .empty) (.node 2297 5069985856653139 .empty .empty)) (.node 2300 3374 (.node 2299 3374 .empty .empty) (.node 2301 3375 .empty .empty))))) (.node 2322 0 (.node 2312 493 (.node 2307 2894 (.node 2305 0 (.node 2304 0 (.node 2303 0 .empty .empty) .empty) (.node 2306 5142556309096560 .empty .empty)) (.node 2310 493 (.node 2309 5087582338713809 (.node 2308 2894 .empty .empty) .empty) (.node 2311 493 .empty .empty))) (.node 2317 495 (.node 2315 494 (.node 2314 494 (.node 2313 5122768858810706 .empty .empty) .empty) (.node 2316 5111775353538995 .empty .empty)) (.node 2320 496 (.node 2319 5109577941289492 (.node 2318 495 .empty .empty) .empty) (.node 2321 496 .empty .empty)))) (.node 2332 2898 (.node 2327 0 (.node 2325 2898 (.node 2324 5120575742577332 (.node 2323 0 .empty .empty) .empty) (.node 2326 2898 .empty .empty)) (.node 2330 5133773104122740 (.node 2329 5140371784895315 (.node 2328 0 .empty .empty) .empty) (.node 2331 2898 .empty .empty))) (.node 2337 0 (.node 2335 0 (.node 2334 0 (.node 2333 2898 .empty .empty) .empty) (.node 2336 0 .empty .empty)) (.node 2339 493 (.node 2338 5151369586183281 .empty .empty) (.node 2340 493 .empty .empty))))))

@[noinline] private def pilotPart55 : RawTree :=
  (.node 2263 496 pilotPart53 pilotPart54)

@[noinline] private def pilotPart56 : RawTree :=
  (.node 2380 495 (.node 2361 3374 (.node 2351 496 (.node 2346 495 (.node 2344 494 (.node 2343 494 (.node 2342 5186556106280178 .empty .empty) .empty) (.node 2345 5175562601008467 .empty .empty)) (.node 2349 496 (.node 2348 5173365188758964 (.node 2347 495 .empty .empty) .empty) (.node 2350 496 .empty .empty))) (.node 2356 0 (.node 2354 3374 (.node 2353 5184362990046804 (.node 2352 0 .empty .empty) .empty) (.node 2355 3374 .empty .empty)) (.node 2359 5197560351592212 (.node 2358 5204159032364787 (.node 2357 0 .empty .empty) .empty) (.node 2360 3374 .empty .empty)))) (.node 2371 493 (.node 2366 0 (.node 2364 0 (.node 2363 0 (.node 2362 3375 .empty .empty) .empty) (.node 2365 0 .empty .empty)) (.node 2369 2894 (.node 2368 2894 (.node 2367 5259137298763792 .empty .empty) .empty) (.node 2370 5221755514425457 .empty .empty))) (.node 2376 494 (.node 2374 5248145941500146 (.node 2373 493 (.node 2372 493 .empty .empty) .empty) (.node 2375 494 .empty .empty)) (.node 2378 495 (.node 2377 5237152436228435 .empty .empty) (.node 2379 495 .empty .empty))))) (.node 2400 495 (.node 2390 0 (.node 2385 0 (.node 2383 496 (.node 2382 496 (.node 2381 5245950677258708 .empty .empty) .empty) (.node 2384 0 .empty .empty)) (.node 2388 0 (.node 2387 0 (.node 2386 5256948478546547 .empty .empty) .empty) (.node 2389 0 .empty .empty))) (.node 2395 5294336706909074 (.node 2393 493 (.node 2392 493 (.node 2391 5267946279834385 .empty .empty) .empty) (.node 2394 493 .empty .empty)) (.node 2398 5283343201637363 (.node 2397 494 (.node 2396 494 .empty .empty) .empty) (.node 2399 495 .empty .empty)))) (.node 2410 0 (.node 2405 496 (.node 2403 496 (.node 2402 5292141442667636 (.node 2401 495 .empty .empty) .empty) (.node 2404 496 .empty .empty)) (.node 2408 0 (.node 2407 5303139243955475 (.node 2406 0 .empty .empty) .empty) (.node 2409 0 .empty .empty))) (.node 2415 2894 (.node 2413 5316336605500880 (.node 2412 5454898159588783 (.node 2411 0 .empty .empty) .empty) (.node 2414 2894 .empty .empty)) (.node 2417 5325134846531153 (.node 2416 2894 .empty .empty) (.node 2418 493 .empty .empty))))))

@[noinline] private def pilotPart57 : RawTree :=
  (.node 2458 0 (.node 2439 2898 (.node 2429 496 (.node 2424 494 (.node 2422 494 (.node 2421 5333933087561426 (.node 2420 493 .empty .empty) .empty) (.node 2423 494 .empty .empty)) (.node 2427 496 (.node 2426 5344930888849268 (.node 2425 5369123903149907 .empty .empty) .empty) (.node 2428 496 .empty .empty))) (.node 2434 2898 (.node 2432 2898 (.node 2431 5355928690137108 (.node 2430 0 .empty .empty) .empty) (.node 2433 2898 .empty .empty)) (.node 2437 2898 (.node 2436 5366926491424948 (.node 2435 0 .empty .empty) .empty) (.node 2438 2898 .empty .empty)))) (.node 2449 493 (.node 2444 2894 (.node 2442 5380123852970352 (.node 2441 0 (.node 2440 0 .empty .empty) .empty) (.node 2443 2894 .empty .empty)) (.node 2447 493 (.node 2446 5388922094000625 (.node 2445 2894 .empty .empty) .empty) (.node 2448 493 .empty .empty))) (.node 2454 5406518576061171 (.node 2452 494 (.node 2451 494 (.node 2450 5397720335030898 .empty .empty) .empty) (.node 2453 494 .empty .empty)) (.node 2456 0 (.node 2455 495 .empty .empty) (.node 2457 0 .empty .empty))))) (.node 2478 0 (.node 2468 494 (.node 2463 5426314618379281 (.node 2461 2894 (.node 2460 2894 (.node 2459 5417516377349008 .empty .empty) .empty) (.node 2462 2894 .empty .empty)) (.node 2466 493 (.node 2465 493 (.node 2464 493 .empty .empty) .empty) (.node 2467 5435112859409554 .empty .empty))) (.node 2473 495 (.node 2471 5452707193462035 (.node 2470 494 (.node 2469 494 .empty .empty) .empty) (.node 2472 495 .empty .empty)) (.node 2476 496 (.node 2475 496 (.node 2474 5450509781212532 .empty .empty) .empty) (.node 2477 496 .empty .empty)))) (.node 2488 5481303624818482 (.node 2483 2894 (.node 2481 2894 (.node 2480 5463707142757936 (.node 2479 0 .empty .empty) .empty) (.node 2482 2894 .empty .empty)) (.node 2486 493 (.node 2485 493 (.node 2484 5472505383788209 .empty .empty) .empty) (.node 2487 493 .empty .empty))) (.node 2493 495 (.node 2491 494 (.node 2490 494 (.node 2489 494 .empty .empty) .empty) (.node 2492 5490101865848755 .empty .empty)) (.node 2495 495 (.node 2494 495 .empty .empty) (.node 2496 0 .empty .empty))))))

@[noinline] private def pilotPart58 : RawTree :=
  (.node 2419 493 pilotPart56 pilotPart57)

@[noinline] private def pilotPart59 : RawTree :=
  (.node 2341 493 pilotPart55 pilotPart58)

@[noinline] private def pilotPart60 : RawTree :=
  (.node 2185 0 pilotPart52 pilotPart59)

@[noinline] private def pilotPart61 : RawTree :=
  (.node 1873 496 pilotPart45 pilotPart60)

@[noinline] private def pilotPart62 : RawTree :=
  (.node 1248 0 pilotPart30 pilotPart61)

private def pilotRecords : RawTree := pilotPart62

def pilotNodes (_fuel : ℕ) (index : Fin 2497) :
    Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut :=
  let code := pilotRecords.get index.val
  if code = 0 then .bound
  else if code < 92161 then
    let tag := code - 1
    .symmetry (EJMGlobalScoreSymmetry.cutOfTag
      ⟨tag / 20 % 4608, Nat.mod_lt _ (by decide)⟩
      ⟨tag % 20, Nat.mod_lt _ (by decide)⟩)
  else
    let payload := code - 92161
    .split ⟨payload % 32 % 20, Nat.mod_lt _ (by decide)⟩
      (fun a => ⟨(payload / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
        Nat.mod_lt _ (by decide)⟩)

def pilotPrefix : Fin 12 → Fin 4 := ![0,0,0,0,0,1,1,1,2,1,1,1]

def pilotCache : Cache :=
  (List.finRange 12).foldl
    (fun cache i => step cache ⟨i.val, by have h := i.isLt; omega⟩ (pilotPrefix i))
    initial

def pilotPartial : Partial (Fin 20) (Fin 4) := fun g =>
  if h : g.val < 12 then some (pilotPrefix ⟨g.val, h⟩) else none

private def cache0 : Cache := pilotCache
private def partial0 : Partial (Fin 20) (Fin 4) := pilotPartial

private def cache1 : Cache :=
  step cache0 ⟨12, by decide⟩ 0
private def partial1 : Partial (Fin 20) (Fin 4) :=
  Function.update partial0 ⟨12, by decide⟩ (some 0)

private def cache2 : Cache :=
  step cache0 ⟨12, by decide⟩ 1
private def partial2 : Partial (Fin 20) (Fin 4) :=
  Function.update partial0 ⟨12, by decide⟩ (some 1)

private def cache3 : Cache :=
  step cache0 ⟨12, by decide⟩ 2
private def partial3 : Partial (Fin 20) (Fin 4) :=
  Function.update partial0 ⟨12, by decide⟩ (some 2)

private def cache4 : Cache :=
  step cache3 ⟨13, by decide⟩ 0
private def partial4 : Partial (Fin 20) (Fin 4) :=
  Function.update partial3 ⟨13, by decide⟩ (some 0)

private def cache5 : Cache :=
  step cache3 ⟨13, by decide⟩ 1
private def partial5 : Partial (Fin 20) (Fin 4) :=
  Function.update partial3 ⟨13, by decide⟩ (some 1)

private def cache6 : Cache :=
  step cache5 ⟨14, by decide⟩ 0
private def partial6 : Partial (Fin 20) (Fin 4) :=
  Function.update partial5 ⟨14, by decide⟩ (some 0)

private def cache7 : Cache :=
  step cache5 ⟨14, by decide⟩ 1
private def partial7 : Partial (Fin 20) (Fin 4) :=
  Function.update partial5 ⟨14, by decide⟩ (some 1)

private def cache8 : Cache :=
  step cache7 ⟨15, by decide⟩ 0
private def partial8 : Partial (Fin 20) (Fin 4) :=
  Function.update partial7 ⟨15, by decide⟩ (some 0)

private def cache9 : Cache :=
  step cache7 ⟨15, by decide⟩ 1
private def partial9 : Partial (Fin 20) (Fin 4) :=
  Function.update partial7 ⟨15, by decide⟩ (some 1)

private def cache10 : Cache :=
  step cache9 ⟨16, by decide⟩ 0
private def partial10 : Partial (Fin 20) (Fin 4) :=
  Function.update partial9 ⟨16, by decide⟩ (some 0)

private def cache11 : Cache :=
  step cache9 ⟨16, by decide⟩ 1
private def partial11 : Partial (Fin 20) (Fin 4) :=
  Function.update partial9 ⟨16, by decide⟩ (some 1)

private def cache12 : Cache :=
  step cache9 ⟨16, by decide⟩ 2
private def partial12 : Partial (Fin 20) (Fin 4) :=
  Function.update partial9 ⟨16, by decide⟩ (some 2)

private def cache73 : Cache :=
  step cache9 ⟨16, by decide⟩ 3
private def partial73 : Partial (Fin 20) (Fin 4) :=
  Function.update partial9 ⟨16, by decide⟩ (some 3)

private def cache134 : Cache :=
  step cache7 ⟨15, by decide⟩ 2
private def partial134 : Partial (Fin 20) (Fin 4) :=
  Function.update partial7 ⟨15, by decide⟩ (some 2)

private def cache135 : Cache :=
  step cache134 ⟨16, by decide⟩ 0
private def partial135 : Partial (Fin 20) (Fin 4) :=
  Function.update partial134 ⟨16, by decide⟩ (some 0)

private def cache136 : Cache :=
  step cache134 ⟨16, by decide⟩ 1
private def partial136 : Partial (Fin 20) (Fin 4) :=
  Function.update partial134 ⟨16, by decide⟩ (some 1)

private def cache137 : Cache :=
  step cache134 ⟨16, by decide⟩ 2
private def partial137 : Partial (Fin 20) (Fin 4) :=
  Function.update partial134 ⟨16, by decide⟩ (some 2)

private def cache194 : Cache :=
  step cache134 ⟨16, by decide⟩ 3
private def partial194 : Partial (Fin 20) (Fin 4) :=
  Function.update partial134 ⟨16, by decide⟩ (some 3)

private def cache251 : Cache :=
  step cache7 ⟨15, by decide⟩ 3
private def partial251 : Partial (Fin 20) (Fin 4) :=
  Function.update partial7 ⟨15, by decide⟩ (some 3)

private def cache252 : Cache :=
  step cache251 ⟨16, by decide⟩ 0
private def partial252 : Partial (Fin 20) (Fin 4) :=
  Function.update partial251 ⟨16, by decide⟩ (some 0)

private def cache253 : Cache :=
  step cache251 ⟨16, by decide⟩ 1
private def partial253 : Partial (Fin 20) (Fin 4) :=
  Function.update partial251 ⟨16, by decide⟩ (some 1)

private def cache254 : Cache :=
  step cache251 ⟨16, by decide⟩ 2
private def partial254 : Partial (Fin 20) (Fin 4) :=
  Function.update partial251 ⟨16, by decide⟩ (some 2)

private def cache315 : Cache :=
  step cache251 ⟨16, by decide⟩ 3
private def partial315 : Partial (Fin 20) (Fin 4) :=
  Function.update partial251 ⟨16, by decide⟩ (some 3)

private def cache376 : Cache :=
  step cache5 ⟨14, by decide⟩ 2
private def partial376 : Partial (Fin 20) (Fin 4) :=
  Function.update partial5 ⟨14, by decide⟩ (some 2)

private def cache377 : Cache :=
  step cache376 ⟨15, by decide⟩ 0
private def partial377 : Partial (Fin 20) (Fin 4) :=
  Function.update partial376 ⟨15, by decide⟩ (some 0)

private def cache378 : Cache :=
  step cache376 ⟨15, by decide⟩ 1
private def partial378 : Partial (Fin 20) (Fin 4) :=
  Function.update partial376 ⟨15, by decide⟩ (some 1)

private def cache379 : Cache :=
  step cache378 ⟨16, by decide⟩ 0
private def partial379 : Partial (Fin 20) (Fin 4) :=
  Function.update partial378 ⟨16, by decide⟩ (some 0)

private def cache380 : Cache :=
  step cache378 ⟨16, by decide⟩ 1
private def partial380 : Partial (Fin 20) (Fin 4) :=
  Function.update partial378 ⟨16, by decide⟩ (some 1)

private def cache381 : Cache :=
  step cache378 ⟨16, by decide⟩ 2
private def partial381 : Partial (Fin 20) (Fin 4) :=
  Function.update partial378 ⟨16, by decide⟩ (some 2)

private def cache406 : Cache :=
  step cache378 ⟨16, by decide⟩ 3
private def partial406 : Partial (Fin 20) (Fin 4) :=
  Function.update partial378 ⟨16, by decide⟩ (some 3)

private def cache447 : Cache :=
  step cache376 ⟨15, by decide⟩ 2
private def partial447 : Partial (Fin 20) (Fin 4) :=
  Function.update partial376 ⟨15, by decide⟩ (some 2)

private def cache448 : Cache :=
  step cache447 ⟨16, by decide⟩ 0
private def partial448 : Partial (Fin 20) (Fin 4) :=
  Function.update partial447 ⟨16, by decide⟩ (some 0)

private def cache449 : Cache :=
  step cache447 ⟨16, by decide⟩ 1
private def partial449 : Partial (Fin 20) (Fin 4) :=
  Function.update partial447 ⟨16, by decide⟩ (some 1)

private def cache450 : Cache :=
  step cache447 ⟨16, by decide⟩ 2
private def partial450 : Partial (Fin 20) (Fin 4) :=
  Function.update partial447 ⟨16, by decide⟩ (some 2)

private def cache487 : Cache :=
  step cache447 ⟨16, by decide⟩ 3
private def partial487 : Partial (Fin 20) (Fin 4) :=
  Function.update partial447 ⟨16, by decide⟩ (some 3)

private def cache528 : Cache :=
  step cache376 ⟨15, by decide⟩ 3
private def partial528 : Partial (Fin 20) (Fin 4) :=
  Function.update partial376 ⟨15, by decide⟩ (some 3)

private def cache529 : Cache :=
  step cache528 ⟨16, by decide⟩ 0
private def partial529 : Partial (Fin 20) (Fin 4) :=
  Function.update partial528 ⟨16, by decide⟩ (some 0)

private def cache530 : Cache :=
  step cache528 ⟨16, by decide⟩ 1
private def partial530 : Partial (Fin 20) (Fin 4) :=
  Function.update partial528 ⟨16, by decide⟩ (some 1)

private def cache531 : Cache :=
  step cache528 ⟨16, by decide⟩ 2
private def partial531 : Partial (Fin 20) (Fin 4) :=
  Function.update partial528 ⟨16, by decide⟩ (some 2)

private def cache572 : Cache :=
  step cache528 ⟨16, by decide⟩ 3
private def partial572 : Partial (Fin 20) (Fin 4) :=
  Function.update partial528 ⟨16, by decide⟩ (some 3)

private def cache625 : Cache :=
  step cache5 ⟨14, by decide⟩ 3
private def partial625 : Partial (Fin 20) (Fin 4) :=
  Function.update partial5 ⟨14, by decide⟩ (some 3)

private def cache626 : Cache :=
  step cache625 ⟨15, by decide⟩ 0
private def partial626 : Partial (Fin 20) (Fin 4) :=
  Function.update partial625 ⟨15, by decide⟩ (some 0)

private def cache627 : Cache :=
  step cache625 ⟨15, by decide⟩ 1
private def partial627 : Partial (Fin 20) (Fin 4) :=
  Function.update partial625 ⟨15, by decide⟩ (some 1)

private def cache628 : Cache :=
  step cache627 ⟨16, by decide⟩ 0
private def partial628 : Partial (Fin 20) (Fin 4) :=
  Function.update partial627 ⟨16, by decide⟩ (some 0)

private def cache629 : Cache :=
  step cache627 ⟨16, by decide⟩ 1
private def partial629 : Partial (Fin 20) (Fin 4) :=
  Function.update partial627 ⟨16, by decide⟩ (some 1)

private def cache630 : Cache :=
  step cache627 ⟨16, by decide⟩ 2
private def partial630 : Partial (Fin 20) (Fin 4) :=
  Function.update partial627 ⟨16, by decide⟩ (some 2)

private def cache659 : Cache :=
  step cache627 ⟨16, by decide⟩ 3
private def partial659 : Partial (Fin 20) (Fin 4) :=
  Function.update partial627 ⟨16, by decide⟩ (some 3)

private def cache692 : Cache :=
  step cache625 ⟨15, by decide⟩ 2
private def partial692 : Partial (Fin 20) (Fin 4) :=
  Function.update partial625 ⟨15, by decide⟩ (some 2)

private def cache693 : Cache :=
  step cache692 ⟨16, by decide⟩ 0
private def partial693 : Partial (Fin 20) (Fin 4) :=
  Function.update partial692 ⟨16, by decide⟩ (some 0)

private def cache694 : Cache :=
  step cache692 ⟨16, by decide⟩ 1
private def partial694 : Partial (Fin 20) (Fin 4) :=
  Function.update partial692 ⟨16, by decide⟩ (some 1)

private def cache695 : Cache :=
  step cache692 ⟨16, by decide⟩ 2
private def partial695 : Partial (Fin 20) (Fin 4) :=
  Function.update partial692 ⟨16, by decide⟩ (some 2)

private def cache744 : Cache :=
  step cache692 ⟨16, by decide⟩ 3
private def partial744 : Partial (Fin 20) (Fin 4) :=
  Function.update partial692 ⟨16, by decide⟩ (some 3)

private def cache781 : Cache :=
  step cache625 ⟨15, by decide⟩ 3
private def partial781 : Partial (Fin 20) (Fin 4) :=
  Function.update partial625 ⟨15, by decide⟩ (some 3)

private def cache782 : Cache :=
  step cache781 ⟨16, by decide⟩ 0
private def partial782 : Partial (Fin 20) (Fin 4) :=
  Function.update partial781 ⟨16, by decide⟩ (some 0)

private def cache783 : Cache :=
  step cache781 ⟨16, by decide⟩ 1
private def partial783 : Partial (Fin 20) (Fin 4) :=
  Function.update partial781 ⟨16, by decide⟩ (some 1)

private def cache784 : Cache :=
  step cache781 ⟨16, by decide⟩ 2
private def partial784 : Partial (Fin 20) (Fin 4) :=
  Function.update partial781 ⟨16, by decide⟩ (some 2)

private def cache821 : Cache :=
  step cache781 ⟨16, by decide⟩ 3
private def partial821 : Partial (Fin 20) (Fin 4) :=
  Function.update partial781 ⟨16, by decide⟩ (some 3)

private def cache858 : Cache :=
  step cache3 ⟨13, by decide⟩ 2
private def partial858 : Partial (Fin 20) (Fin 4) :=
  Function.update partial3 ⟨13, by decide⟩ (some 2)

private def cache859 : Cache :=
  step cache858 ⟨14, by decide⟩ 0
private def partial859 : Partial (Fin 20) (Fin 4) :=
  Function.update partial858 ⟨14, by decide⟩ (some 0)

private def cache860 : Cache :=
  step cache859 ⟨15, by decide⟩ 0
private def partial860 : Partial (Fin 20) (Fin 4) :=
  Function.update partial859 ⟨15, by decide⟩ (some 0)

private def cache861 : Cache :=
  step cache859 ⟨15, by decide⟩ 1
private def partial861 : Partial (Fin 20) (Fin 4) :=
  Function.update partial859 ⟨15, by decide⟩ (some 1)

private def cache862 : Cache :=
  step cache859 ⟨15, by decide⟩ 2
private def partial862 : Partial (Fin 20) (Fin 4) :=
  Function.update partial859 ⟨15, by decide⟩ (some 2)

private def cache863 : Cache :=
  step cache862 ⟨16, by decide⟩ 0
private def partial863 : Partial (Fin 20) (Fin 4) :=
  Function.update partial862 ⟨16, by decide⟩ (some 0)

private def cache864 : Cache :=
  step cache862 ⟨16, by decide⟩ 1
private def partial864 : Partial (Fin 20) (Fin 4) :=
  Function.update partial862 ⟨16, by decide⟩ (some 1)

private def cache865 : Cache :=
  step cache862 ⟨16, by decide⟩ 2
private def partial865 : Partial (Fin 20) (Fin 4) :=
  Function.update partial862 ⟨16, by decide⟩ (some 2)

private def cache906 : Cache :=
  step cache862 ⟨16, by decide⟩ 3
private def partial906 : Partial (Fin 20) (Fin 4) :=
  Function.update partial862 ⟨16, by decide⟩ (some 3)

private def cache955 : Cache :=
  step cache859 ⟨15, by decide⟩ 3
private def partial955 : Partial (Fin 20) (Fin 4) :=
  Function.update partial859 ⟨15, by decide⟩ (some 3)

private def cache956 : Cache :=
  step cache955 ⟨16, by decide⟩ 0
private def partial956 : Partial (Fin 20) (Fin 4) :=
  Function.update partial955 ⟨16, by decide⟩ (some 0)

private def cache957 : Cache :=
  step cache955 ⟨16, by decide⟩ 1
private def partial957 : Partial (Fin 20) (Fin 4) :=
  Function.update partial955 ⟨16, by decide⟩ (some 1)

private def cache958 : Cache :=
  step cache955 ⟨16, by decide⟩ 2
private def partial958 : Partial (Fin 20) (Fin 4) :=
  Function.update partial955 ⟨16, by decide⟩ (some 2)

private def cache1003 : Cache :=
  step cache955 ⟨16, by decide⟩ 3
private def partial1003 : Partial (Fin 20) (Fin 4) :=
  Function.update partial955 ⟨16, by decide⟩ (some 3)

private def cache1064 : Cache :=
  step cache858 ⟨14, by decide⟩ 1
private def partial1064 : Partial (Fin 20) (Fin 4) :=
  Function.update partial858 ⟨14, by decide⟩ (some 1)

private def cache1065 : Cache :=
  step cache1064 ⟨15, by decide⟩ 0
private def partial1065 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1064 ⟨15, by decide⟩ (some 0)

private def cache1066 : Cache :=
  step cache1064 ⟨15, by decide⟩ 1
private def partial1066 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1064 ⟨15, by decide⟩ (some 1)

private def cache1067 : Cache :=
  step cache1064 ⟨15, by decide⟩ 2
private def partial1067 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1064 ⟨15, by decide⟩ (some 2)

private def cache1068 : Cache :=
  step cache1067 ⟨16, by decide⟩ 0
private def partial1068 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1067 ⟨16, by decide⟩ (some 0)

private def cache1069 : Cache :=
  step cache1067 ⟨16, by decide⟩ 1
private def partial1069 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1067 ⟨16, by decide⟩ (some 1)

private def cache1070 : Cache :=
  step cache1067 ⟨16, by decide⟩ 2
private def partial1070 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1067 ⟨16, by decide⟩ (some 2)

private def cache1091 : Cache :=
  step cache1067 ⟨16, by decide⟩ 3
private def partial1091 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1067 ⟨16, by decide⟩ (some 3)

private def cache1136 : Cache :=
  step cache1064 ⟨15, by decide⟩ 3
private def partial1136 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1064 ⟨15, by decide⟩ (some 3)

private def cache1137 : Cache :=
  step cache1136 ⟨16, by decide⟩ 0
private def partial1137 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1136 ⟨16, by decide⟩ (some 0)

private def cache1138 : Cache :=
  step cache1136 ⟨16, by decide⟩ 1
private def partial1138 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1136 ⟨16, by decide⟩ (some 1)

private def cache1139 : Cache :=
  step cache1136 ⟨16, by decide⟩ 2
private def partial1139 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1136 ⟨16, by decide⟩ (some 2)

private def cache1168 : Cache :=
  step cache1136 ⟨16, by decide⟩ 3
private def partial1168 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1136 ⟨16, by decide⟩ (some 3)

private def cache1209 : Cache :=
  step cache858 ⟨14, by decide⟩ 2
private def partial1209 : Partial (Fin 20) (Fin 4) :=
  Function.update partial858 ⟨14, by decide⟩ (some 2)

private def cache1210 : Cache :=
  step cache1209 ⟨15, by decide⟩ 0
private def partial1210 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1209 ⟨15, by decide⟩ (some 0)

private def cache1211 : Cache :=
  step cache1209 ⟨15, by decide⟩ 1
private def partial1211 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1209 ⟨15, by decide⟩ (some 1)

private def cache1212 : Cache :=
  step cache1209 ⟨15, by decide⟩ 2
private def partial1212 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1209 ⟨15, by decide⟩ (some 2)

private def cache1213 : Cache :=
  step cache1212 ⟨16, by decide⟩ 0
private def partial1213 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1212 ⟨16, by decide⟩ (some 0)

private def cache1214 : Cache :=
  step cache1212 ⟨16, by decide⟩ 1
private def partial1214 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1212 ⟨16, by decide⟩ (some 1)

private def cache1215 : Cache :=
  step cache1212 ⟨16, by decide⟩ 2
private def partial1215 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1212 ⟨16, by decide⟩ (some 2)

private def cache1240 : Cache :=
  step cache1212 ⟨16, by decide⟩ 3
private def partial1240 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1212 ⟨16, by decide⟩ (some 3)

private def cache1289 : Cache :=
  step cache1209 ⟨15, by decide⟩ 3
private def partial1289 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1209 ⟨15, by decide⟩ (some 3)

private def cache1290 : Cache :=
  step cache1289 ⟨16, by decide⟩ 0
private def partial1290 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1289 ⟨16, by decide⟩ (some 0)

private def cache1291 : Cache :=
  step cache1289 ⟨16, by decide⟩ 1
private def partial1291 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1289 ⟨16, by decide⟩ (some 1)

private def cache1292 : Cache :=
  step cache1289 ⟨16, by decide⟩ 2
private def partial1292 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1289 ⟨16, by decide⟩ (some 2)

private def cache1325 : Cache :=
  step cache1289 ⟨16, by decide⟩ 3
private def partial1325 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1289 ⟨16, by decide⟩ (some 3)

private def cache1370 : Cache :=
  step cache858 ⟨14, by decide⟩ 3
private def partial1370 : Partial (Fin 20) (Fin 4) :=
  Function.update partial858 ⟨14, by decide⟩ (some 3)

private def cache1371 : Cache :=
  step cache1370 ⟨15, by decide⟩ 0
private def partial1371 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1370 ⟨15, by decide⟩ (some 0)

private def cache1372 : Cache :=
  step cache1370 ⟨15, by decide⟩ 1
private def partial1372 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1370 ⟨15, by decide⟩ (some 1)

private def cache1373 : Cache :=
  step cache1370 ⟨15, by decide⟩ 2
private def partial1373 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1370 ⟨15, by decide⟩ (some 2)

private def cache1374 : Cache :=
  step cache1373 ⟨16, by decide⟩ 0
private def partial1374 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1373 ⟨16, by decide⟩ (some 0)

private def cache1375 : Cache :=
  step cache1373 ⟨16, by decide⟩ 1
private def partial1375 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1373 ⟨16, by decide⟩ (some 1)

private def cache1376 : Cache :=
  step cache1373 ⟨16, by decide⟩ 2
private def partial1376 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1373 ⟨16, by decide⟩ (some 2)

private def cache1401 : Cache :=
  step cache1373 ⟨16, by decide⟩ 3
private def partial1401 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1373 ⟨16, by decide⟩ (some 3)

private def cache1438 : Cache :=
  step cache1370 ⟨15, by decide⟩ 3
private def partial1438 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1370 ⟨15, by decide⟩ (some 3)

private def cache1439 : Cache :=
  step cache1438 ⟨16, by decide⟩ 0
private def partial1439 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1438 ⟨16, by decide⟩ (some 0)

private def cache1440 : Cache :=
  step cache1438 ⟨16, by decide⟩ 1
private def partial1440 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1438 ⟨16, by decide⟩ (some 1)

private def cache1441 : Cache :=
  step cache1438 ⟨16, by decide⟩ 2
private def partial1441 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1438 ⟨16, by decide⟩ (some 2)

private def cache1466 : Cache :=
  step cache1438 ⟨16, by decide⟩ 3
private def partial1466 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1438 ⟨16, by decide⟩ (some 3)

private def cache1507 : Cache :=
  step cache3 ⟨13, by decide⟩ 3
private def partial1507 : Partial (Fin 20) (Fin 4) :=
  Function.update partial3 ⟨13, by decide⟩ (some 3)

private def cache1508 : Cache :=
  step cache1507 ⟨14, by decide⟩ 0
private def partial1508 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1507 ⟨14, by decide⟩ (some 0)

private def cache1509 : Cache :=
  step cache1508 ⟨15, by decide⟩ 0
private def partial1509 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1508 ⟨15, by decide⟩ (some 0)

private def cache1510 : Cache :=
  step cache1508 ⟨15, by decide⟩ 1
private def partial1510 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1508 ⟨15, by decide⟩ (some 1)

private def cache1511 : Cache :=
  step cache1508 ⟨15, by decide⟩ 2
private def partial1511 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1508 ⟨15, by decide⟩ (some 2)

private def cache1512 : Cache :=
  step cache1508 ⟨15, by decide⟩ 3
private def partial1512 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1508 ⟨15, by decide⟩ (some 3)

private def cache1513 : Cache :=
  step cache1512 ⟨16, by decide⟩ 0
private def partial1513 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1512 ⟨16, by decide⟩ (some 0)

private def cache1514 : Cache :=
  step cache1512 ⟨16, by decide⟩ 1
private def partial1514 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1512 ⟨16, by decide⟩ (some 1)

private def cache1515 : Cache :=
  step cache1512 ⟨16, by decide⟩ 2
private def partial1515 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1512 ⟨16, by decide⟩ (some 2)

private def cache1540 : Cache :=
  step cache1512 ⟨16, by decide⟩ 3
private def partial1540 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1512 ⟨16, by decide⟩ (some 3)

private def cache1597 : Cache :=
  step cache1507 ⟨14, by decide⟩ 1
private def partial1597 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1507 ⟨14, by decide⟩ (some 1)

private def cache1658 : Cache :=
  step cache1507 ⟨14, by decide⟩ 2
private def partial1658 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1507 ⟨14, by decide⟩ (some 2)

private def cache1659 : Cache :=
  step cache1658 ⟨15, by decide⟩ 0
private def partial1659 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1658 ⟨15, by decide⟩ (some 0)

private def cache1660 : Cache :=
  step cache1658 ⟨15, by decide⟩ 1
private def partial1660 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1658 ⟨15, by decide⟩ (some 1)

private def cache1661 : Cache :=
  step cache1658 ⟨15, by decide⟩ 2
private def partial1661 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1658 ⟨15, by decide⟩ (some 2)

private def cache1662 : Cache :=
  step cache1658 ⟨15, by decide⟩ 3
private def partial1662 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1658 ⟨15, by decide⟩ (some 3)

private def cache1663 : Cache :=
  step cache1662 ⟨16, by decide⟩ 0
private def partial1663 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1662 ⟨16, by decide⟩ (some 0)

private def cache1664 : Cache :=
  step cache1662 ⟨16, by decide⟩ 1
private def partial1664 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1662 ⟨16, by decide⟩ (some 1)

private def cache1665 : Cache :=
  step cache1662 ⟨16, by decide⟩ 2
private def partial1665 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1662 ⟨16, by decide⟩ (some 2)

private def cache1682 : Cache :=
  step cache1662 ⟨16, by decide⟩ 3
private def partial1682 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1662 ⟨16, by decide⟩ (some 3)

private def cache1739 : Cache :=
  step cache1507 ⟨14, by decide⟩ 3
private def partial1739 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1507 ⟨14, by decide⟩ (some 3)

private def cache1792 : Cache :=
  step cache0 ⟨12, by decide⟩ 3
private def partial1792 : Partial (Fin 20) (Fin 4) :=
  Function.update partial0 ⟨12, by decide⟩ (some 3)

private def cache1793 : Cache :=
  step cache1792 ⟨13, by decide⟩ 0
private def partial1793 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1792 ⟨13, by decide⟩ (some 0)

private def cache1794 : Cache :=
  step cache1792 ⟨13, by decide⟩ 1
private def partial1794 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1792 ⟨13, by decide⟩ (some 1)

private def cache1795 : Cache :=
  step cache1794 ⟨14, by decide⟩ 0
private def partial1795 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1794 ⟨14, by decide⟩ (some 0)

private def cache1796 : Cache :=
  step cache1794 ⟨14, by decide⟩ 1
private def partial1796 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1794 ⟨14, by decide⟩ (some 1)

private def cache1797 : Cache :=
  step cache1796 ⟨15, by decide⟩ 0
private def partial1797 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1796 ⟨15, by decide⟩ (some 0)

private def cache1798 : Cache :=
  step cache1796 ⟨15, by decide⟩ 1
private def partial1798 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1796 ⟨15, by decide⟩ (some 1)

private def cache1803 : Cache :=
  step cache1796 ⟨15, by decide⟩ 2
private def partial1803 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1796 ⟨15, by decide⟩ (some 2)

private def cache1864 : Cache :=
  step cache1796 ⟨15, by decide⟩ 3
private def partial1864 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1796 ⟨15, by decide⟩ (some 3)

private def cache1909 : Cache :=
  step cache1794 ⟨14, by decide⟩ 2
private def partial1909 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1794 ⟨14, by decide⟩ (some 2)

private def cache1910 : Cache :=
  step cache1909 ⟨15, by decide⟩ 0
private def partial1910 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1909 ⟨15, by decide⟩ (some 0)

private def cache1911 : Cache :=
  step cache1909 ⟨15, by decide⟩ 1
private def partial1911 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1909 ⟨15, by decide⟩ (some 1)

private def cache1952 : Cache :=
  step cache1909 ⟨15, by decide⟩ 2
private def partial1952 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1909 ⟨15, by decide⟩ (some 2)

private def cache1997 : Cache :=
  step cache1909 ⟨15, by decide⟩ 3
private def partial1997 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1909 ⟨15, by decide⟩ (some 3)

private def cache2038 : Cache :=
  step cache1794 ⟨14, by decide⟩ 3
private def partial2038 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1794 ⟨14, by decide⟩ (some 3)

private def cache2039 : Cache :=
  step cache2038 ⟨15, by decide⟩ 0
private def partial2039 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2038 ⟨15, by decide⟩ (some 0)

private def cache2040 : Cache :=
  step cache2038 ⟨15, by decide⟩ 1
private def partial2040 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2038 ⟨15, by decide⟩ (some 1)

private def cache2081 : Cache :=
  step cache2038 ⟨15, by decide⟩ 2
private def partial2081 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2038 ⟨15, by decide⟩ (some 2)

private def cache2130 : Cache :=
  step cache2038 ⟨15, by decide⟩ 3
private def partial2130 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2038 ⟨15, by decide⟩ (some 3)

private def cache2159 : Cache :=
  step cache1792 ⟨13, by decide⟩ 2
private def partial2159 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1792 ⟨13, by decide⟩ (some 2)

private def cache2160 : Cache :=
  step cache2159 ⟨14, by decide⟩ 0
private def partial2160 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2159 ⟨14, by decide⟩ (some 0)

private def cache2161 : Cache :=
  step cache2160 ⟨15, by decide⟩ 0
private def partial2161 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2160 ⟨15, by decide⟩ (some 0)

private def cache2162 : Cache :=
  step cache2160 ⟨15, by decide⟩ 1
private def partial2162 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2160 ⟨15, by decide⟩ (some 1)

private def cache2163 : Cache :=
  step cache2160 ⟨15, by decide⟩ 2
private def partial2163 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2160 ⟨15, by decide⟩ (some 2)

private def cache2204 : Cache :=
  step cache2160 ⟨15, by decide⟩ 3
private def partial2204 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2160 ⟨15, by decide⟩ (some 3)

private def cache2249 : Cache :=
  step cache2159 ⟨14, by decide⟩ 1
private def partial2249 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2159 ⟨14, by decide⟩ (some 1)

private def cache2306 : Cache :=
  step cache2159 ⟨14, by decide⟩ 2
private def partial2306 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2159 ⟨14, by decide⟩ (some 2)

private def cache2367 : Cache :=
  step cache2159 ⟨14, by decide⟩ 3
private def partial2367 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2159 ⟨14, by decide⟩ (some 3)

private def cache2412 : Cache :=
  step cache1792 ⟨13, by decide⟩ 3
private def partial2412 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1792 ⟨13, by decide⟩ (some 3)

private def cache2413 : Cache :=
  step cache2412 ⟨14, by decide⟩ 0
private def partial2413 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2412 ⟨14, by decide⟩ (some 0)

private def cache2442 : Cache :=
  step cache2412 ⟨14, by decide⟩ 1
private def partial2442 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2412 ⟨14, by decide⟩ (some 1)

private def cache2459 : Cache :=
  step cache2412 ⟨14, by decide⟩ 2
private def partial2459 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2412 ⟨14, by decide⟩ (some 2)

private def cache2480 : Cache :=
  step cache2412 ⟨14, by decide⟩ 3
private def partial2480 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2412 ⟨14, by decide⟩ (some 3)

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/Users/macstudio/omega/trureturing-01a12631-expectation-fix/.ejm-global-suffix-boundary2/progress.txt" "definitions-accepted\n"
set_option trace.profiler true in
private theorem actual_cache_lower : lower cache2480 = (-72642642605226330) := by
  decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/Users/macstudio/omega/trureturing-01a12631-expectation-fix/.ejm-global-suffix-boundary2/progress.txt" "actual-cache-lower-accepted\n"
set_option trace.profiler true in
private theorem actual_symmetry_leaf :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates scale 5
      ⟨2481, by decide⟩ (step cache2480 ⟨15, by decide⟩ 0)
      (Function.update partial2480 ⟨15, by decide⟩ (some 0)) = true := by
  decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/Users/macstudio/omega/trureturing-01a12631-expectation-fix/.ejm-global-suffix-boundary2/progress.txt" "lower-and-symmetry-leaf-accepted\n"
#print axioms actual_cache_lower
#print axioms actual_symmetry_leaf
end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixBoundaryProbe2
