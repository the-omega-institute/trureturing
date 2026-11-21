/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Main06
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main06.chunk_checked
   digest: Exact numerical and binary coverage certificate for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainSupport

/-! Opaque numerical subproofs bound temporary kernel reduction memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.Main06

private abbrev C (lo hi : Fin 7 → ℕ) (tree : MainTree) : Prop :=
  checkExponentBoxTree mainScale boxPrimes lo hi tree = true

/-- Lower exponents at this subtree root. -/
def lo : Fin 7 → ℕ := ![4, 2, 0, 0, 0, 0, 0]

/-- Upper exponents at the same root. -/
def hi : Fin 7 → ℕ := ![8, 7, 1, 0, 1, 1, 1]

private def n2433 : MainTree := .leaf (mainFullLeaf ![4, 2, 0, 0, 0, 0, 0])
private def n2434 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 0, 0, 0, 0])
private def n2432 : MainTree := .split 0 4 n2433 n2434
private def n2436 : MainTree := .leaf (mainGapLeaf ![4, 3, 0, 0, 0, 0, 0])
private def n2437 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 0, 0, 0, 0])
private def n2435 : MainTree := .split 0 4 n2436 n2437
private def n2431 : MainTree := .split 1 2 n2432 n2435
private def n2439 : MainTree := .leaf (mainGapLeaf ![8, 2, 0, 0, 0, 0, 0])
private def n2440 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 0, 0, 0, 0])
private def n2438 : MainTree := .split 1 2 n2439 n2440
private def n2430 : MainTree := .split 0 5 n2431 n2438
private def n2444 : MainTree := .leaf (mainGapLeaf ![4, 2, 0, 0, 0, 0, 1])
private def n2445 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 0, 0, 0, 1])
private def n2443 : MainTree := .split 0 4 n2444 n2445
private def n2446 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 0, 0, 0, 1])
private def n2442 : MainTree := .split 1 2 n2443 n2446
private def n2447 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 0, 0, 0, 1])
private def n2441 : MainTree := .split 0 5 n2442 n2447
private def n2429 : MainTree := .split 6 0 n2430 n2441
private def n2451 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 0, 0, 1, 0])
private def n2452 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 0, 0, 1, 0])
private def n2450 : MainTree := .split 1 2 n2451 n2452
private def n2454 : MainTree := .leaf (mainGapLeaf ![8, 2, 0, 0, 0, 1, 0])
private def n2455 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 0, 0, 1, 0])
private def n2453 : MainTree := .split 1 2 n2454 n2455
private def n2449 : MainTree := .split 0 5 n2450 n2453
private def n2458 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 0, 0, 1, 1])
private def n2459 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 0, 0, 1, 1])
private def n2457 : MainTree := .split 1 2 n2458 n2459
private def n2460 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 0, 0, 1, 1])
private def n2456 : MainTree := .split 0 5 n2457 n2460
private def n2448 : MainTree := .split 6 0 n2449 n2456
private def n2428 : MainTree := .split 5 0 n2429 n2448
private def n2466 : MainTree := .leaf (mainGapLeaf ![4, 2, 0, 0, 1, 0, 0])
private def n2467 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 0, 1, 0, 0])
private def n2465 : MainTree := .split 0 4 n2466 n2467
private def n2468 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 0, 1, 0, 0])
private def n2464 : MainTree := .split 1 2 n2465 n2468
private def n2470 : MainTree := .leaf (mainGapLeaf ![8, 2, 0, 0, 1, 0, 0])
private def n2471 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 0, 1, 0, 0])
private def n2469 : MainTree := .split 1 2 n2470 n2471
private def n2463 : MainTree := .split 0 5 n2464 n2469
private def n2474 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 0, 1, 0, 1])
private def n2475 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 0, 1, 0, 1])
private def n2473 : MainTree := .split 1 2 n2474 n2475
private def n2476 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 0, 1, 0, 1])
private def n2472 : MainTree := .split 0 5 n2473 n2476
private def n2462 : MainTree := .split 6 0 n2463 n2472
private def n2480 : MainTree := .leaf (mainGapLeaf ![5, 2, 0, 0, 1, 1, 0])
private def n2481 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 0, 1, 1, 0])
private def n2479 : MainTree := .split 1 2 n2480 n2481
private def n2482 : MainTree := .leaf (mainRankLeaf 1 ![8, 3, 0, 0, 1, 1, 0])
private def n2478 : MainTree := .split 0 5 n2479 n2482
private def n2484 : MainTree := .leaf (mainGapLeaf ![5, 3, 0, 0, 1, 1, 1])
private def n2485 : MainTree := .leaf (mainGapLeaf ![8, 3, 0, 0, 1, 1, 1])
private def n2483 : MainTree := .split 0 5 n2484 n2485
private def n2477 : MainTree := .split 6 0 n2478 n2483
private def n2461 : MainTree := .split 5 0 n2462 n2477
private def n2427 : MainTree := .split 4 0 n2428 n2461
private def n2492 : MainTree := .leaf (mainFullLeaf ![4, 2, 1, 0, 0, 0, 0])
private def n2493 : MainTree := .leaf (mainFullLeaf ![5, 2, 1, 0, 0, 0, 0])
private def n2491 : MainTree := .split 0 4 n2492 n2493
private def n2495 : MainTree := .leaf (mainFullLeaf ![4, 3, 1, 0, 0, 0, 0])
private def n2496 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 0, 0, 0, 0])
private def n2494 : MainTree := .split 0 4 n2495 n2496
private def n2490 : MainTree := .split 1 2 n2491 n2494
private def n2499 : MainTree := .leaf (mainRankLeaf 2 ![6, 2, 1, 0, 0, 0, 0])
private def n2500 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 0, 0, 0, 0])
private def n2498 : MainTree := .split 0 6 n2499 n2500
private def n2501 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 0, 0, 0, 0])
private def n2497 : MainTree := .split 1 2 n2498 n2501
private def n2489 : MainTree := .split 0 5 n2490 n2497
private def n2505 : MainTree := .leaf (mainGapLeaf ![4, 2, 1, 0, 0, 0, 1])
private def n2506 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 0, 0, 0, 1])
private def n2504 : MainTree := .split 0 4 n2505 n2506
private def n2507 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 0, 0, 0, 1])
private def n2503 : MainTree := .split 1 2 n2504 n2507
private def n2509 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 0, 0, 0, 1])
private def n2510 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 0, 0, 0, 1])
private def n2508 : MainTree := .split 1 2 n2509 n2510
private def n2502 : MainTree := .split 0 5 n2503 n2508
private def n2488 : MainTree := .split 6 0 n2489 n2502
private def n2515 : MainTree := .leaf (mainRankLeaf 2 ![4, 2, 1, 0, 0, 1, 0])
private def n2516 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 0, 0, 1, 0])
private def n2514 : MainTree := .split 0 4 n2515 n2516
private def n2518 : MainTree := .leaf (mainGapLeaf ![4, 3, 1, 0, 0, 1, 0])
private def n2519 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 0, 0, 1, 0])
private def n2517 : MainTree := .split 0 4 n2518 n2519
private def n2513 : MainTree := .split 1 2 n2514 n2517
private def n2521 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 0, 0, 1, 0])
private def n2522 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 0, 0, 1, 0])
private def n2520 : MainTree := .split 1 2 n2521 n2522
private def n2512 : MainTree := .split 0 5 n2513 n2520
private def n2525 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 0, 0, 1, 1])
private def n2526 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 0, 0, 1, 1])
private def n2524 : MainTree := .split 1 2 n2525 n2526
private def n2527 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 0, 0, 1, 1])
private def n2523 : MainTree := .split 0 5 n2524 n2527
private def n2511 : MainTree := .split 6 0 n2512 n2523
private def n2487 : MainTree := .split 5 0 n2488 n2511
private def n2533 : MainTree := .leaf (mainFullLeaf ![4, 2, 1, 0, 1, 0, 0])
private def n2534 : MainTree := .leaf (mainRankLeaf 2 ![5, 2, 1, 0, 1, 0, 0])
private def n2532 : MainTree := .split 0 4 n2533 n2534
private def n2536 : MainTree := .leaf (mainGapLeaf ![4, 3, 1, 0, 1, 0, 0])
private def n2537 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 0, 1, 0, 0])
private def n2535 : MainTree := .split 0 4 n2536 n2537
private def n2531 : MainTree := .split 1 2 n2532 n2535
private def n2540 : MainTree := .leaf (mainGapLeaf ![6, 2, 1, 0, 1, 0, 0])
private def n2541 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 0, 1, 0, 0])
private def n2539 : MainTree := .split 0 6 n2540 n2541
private def n2542 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 0, 1, 0, 0])
private def n2538 : MainTree := .split 1 2 n2539 n2542
private def n2530 : MainTree := .split 0 5 n2531 n2538
private def n2545 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 0, 1, 0, 1])
private def n2546 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 0, 1, 0, 1])
private def n2544 : MainTree := .split 1 2 n2545 n2546
private def n2547 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 0, 1, 0, 1])
private def n2543 : MainTree := .split 0 5 n2544 n2547
private def n2529 : MainTree := .split 6 0 n2530 n2543
private def n2552 : MainTree := .leaf (mainGapLeaf ![4, 2, 1, 0, 1, 1, 0])
private def n2553 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 0, 1, 1, 0])
private def n2551 : MainTree := .split 0 4 n2552 n2553
private def n2555 : MainTree := .leaf (mainGapLeaf ![4, 3, 1, 0, 1, 1, 0])
private def n2556 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 0, 1, 1, 0])
private def n2554 : MainTree := .split 0 4 n2555 n2556
private def n2550 : MainTree := .split 1 2 n2551 n2554
private def n2558 : MainTree := .leaf (mainGapLeaf ![8, 2, 1, 0, 1, 1, 0])
private def n2559 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 0, 1, 1, 0])
private def n2557 : MainTree := .split 1 2 n2558 n2559
private def n2549 : MainTree := .split 0 5 n2550 n2557
private def n2562 : MainTree := .leaf (mainGapLeaf ![5, 2, 1, 0, 1, 1, 1])
private def n2563 : MainTree := .leaf (mainGapLeaf ![5, 3, 1, 0, 1, 1, 1])
private def n2561 : MainTree := .split 1 2 n2562 n2563
private def n2564 : MainTree := .leaf (mainGapLeaf ![8, 3, 1, 0, 1, 1, 1])
private def n2560 : MainTree := .split 0 5 n2561 n2564
private def n2548 : MainTree := .split 6 0 n2549 n2560
private def n2528 : MainTree := .split 5 0 n2529 n2548
private def n2486 : MainTree := .split 4 0 n2487 n2528
private def n2426 : MainTree := .split 2 0 n2427 n2486
private def n2570 : MainTree := .leaf (mainGapLeaf ![5, 7, 0, 0, 0, 0, 0])
private def n2571 : MainTree := .leaf (mainGapLeaf ![8, 7, 0, 0, 0, 0, 0])
private def n2569 : MainTree := .split 0 5 n2570 n2571
private def n2572 : MainTree := .leaf (mainGapLeaf ![8, 7, 0, 0, 0, 0, 1])
private def n2568 : MainTree := .split 6 0 n2569 n2572
private def n2574 : MainTree := .leaf (mainGapLeaf ![8, 7, 0, 0, 0, 1, 0])
private def n2575 : MainTree := .leaf (mainGapLeaf ![8, 7, 0, 0, 0, 1, 1])
private def n2573 : MainTree := .split 6 0 n2574 n2575
private def n2567 : MainTree := .split 5 0 n2568 n2573
private def n2579 : MainTree := .leaf (mainGapLeaf ![5, 7, 0, 0, 1, 0, 0])
private def n2580 : MainTree := .leaf (mainGapLeaf ![8, 7, 0, 0, 1, 0, 0])
private def n2578 : MainTree := .split 0 5 n2579 n2580
private def n2581 : MainTree := .leaf (mainGapLeaf ![8, 7, 0, 0, 1, 0, 1])
private def n2577 : MainTree := .split 6 0 n2578 n2581
private def n2583 : MainTree := .leaf (mainRankLeaf 1 ![8, 7, 0, 0, 1, 1, 0])
private def n2584 : MainTree := .leaf (mainGapLeaf ![8, 7, 0, 0, 1, 1, 1])
private def n2582 : MainTree := .split 6 0 n2583 n2584
private def n2576 : MainTree := .split 5 0 n2577 n2582
private def n2566 : MainTree := .split 4 0 n2567 n2576
private def n2592 : MainTree := .leaf (mainGapLeaf ![4, 4, 1, 0, 0, 0, 0])
private def n2593 : MainTree := .leaf (mainGapLeaf ![4, 5, 1, 0, 0, 0, 0])
private def n2591 : MainTree := .split 1 4 n2592 n2593
private def n2594 : MainTree := .leaf (mainGapLeaf ![5, 5, 1, 0, 0, 0, 0])
private def n2590 : MainTree := .split 0 4 n2591 n2594
private def n2595 : MainTree := .leaf (mainGapLeaf ![5, 7, 1, 0, 0, 0, 0])
private def n2589 : MainTree := .split 1 5 n2590 n2595
private def n2596 : MainTree := .leaf (mainGapLeaf ![8, 7, 1, 0, 0, 0, 0])
private def n2588 : MainTree := .split 0 5 n2589 n2596
private def n2598 : MainTree := .leaf (mainGapLeaf ![5, 7, 1, 0, 0, 0, 1])
private def n2599 : MainTree := .leaf (mainGapLeaf ![8, 7, 1, 0, 0, 0, 1])
private def n2597 : MainTree := .split 0 5 n2598 n2599
private def n2587 : MainTree := .split 6 0 n2588 n2597
private def n2603 : MainTree := .leaf (mainGapLeaf ![5, 5, 1, 0, 0, 1, 0])
private def n2604 : MainTree := .leaf (mainGapLeaf ![5, 7, 1, 0, 0, 1, 0])
private def n2602 : MainTree := .split 1 5 n2603 n2604
private def n2605 : MainTree := .leaf (mainGapLeaf ![8, 7, 1, 0, 0, 1, 0])
private def n2601 : MainTree := .split 0 5 n2602 n2605
private def n2606 : MainTree := .leaf (mainGapLeaf ![8, 7, 1, 0, 0, 1, 1])
private def n2600 : MainTree := .split 6 0 n2601 n2606
private def n2586 : MainTree := .split 5 0 n2587 n2600
private def n2612 : MainTree := .leaf (mainGapLeaf ![4, 5, 1, 0, 1, 0, 0])
private def n2613 : MainTree := .leaf (mainGapLeaf ![5, 5, 1, 0, 1, 0, 0])
private def n2611 : MainTree := .split 0 4 n2612 n2613
private def n2614 : MainTree := .leaf (mainGapLeaf ![5, 7, 1, 0, 1, 0, 0])
private def n2610 : MainTree := .split 1 5 n2611 n2614
private def n2615 : MainTree := .leaf (mainGapLeaf ![8, 7, 1, 0, 1, 0, 0])
private def n2609 : MainTree := .split 0 5 n2610 n2615
private def n2616 : MainTree := .leaf (mainGapLeaf ![8, 7, 1, 0, 1, 0, 1])
private def n2608 : MainTree := .split 6 0 n2609 n2616
private def n2619 : MainTree := .leaf (mainGapLeaf ![5, 7, 1, 0, 1, 1, 0])
private def n2620 : MainTree := .leaf (mainGapLeaf ![8, 7, 1, 0, 1, 1, 0])
private def n2618 : MainTree := .split 0 5 n2619 n2620
private def n2621 : MainTree := .leaf (mainGapLeaf ![8, 7, 1, 0, 1, 1, 1])
private def n2617 : MainTree := .split 6 0 n2618 n2621
private def n2607 : MainTree := .split 5 0 n2608 n2617
private def n2585 : MainTree := .split 4 0 n2586 n2607
private def n2565 : MainTree := .split 2 0 n2566 n2585
private def n2425 : MainTree := .split 1 3 n2426 n2565

private theorem c2428 : C ![4, 2, 0, 0, 0, 0, 0] ![8, 3, 0, 0, 0, 1, 1] n2428 := by
  decide +kernel

private theorem c2461 : C ![4, 2, 0, 0, 1, 0, 0] ![8, 3, 0, 0, 1, 1, 1] n2461 := by
  decide +kernel

private theorem c2427 : C ![4, 2, 0, 0, 0, 0, 0] ![8, 3, 0, 0, 1, 1, 1] n2427 := by
  exact checkExponentBoxTree_join c2428 c2461 (by decide +kernel)

private theorem c2488 : C ![4, 2, 1, 0, 0, 0, 0] ![8, 3, 1, 0, 0, 0, 1] n2488 := by
  decide +kernel

private theorem c2511 : C ![4, 2, 1, 0, 0, 1, 0] ![8, 3, 1, 0, 0, 1, 1] n2511 := by
  decide +kernel

private theorem c2487 : C ![4, 2, 1, 0, 0, 0, 0] ![8, 3, 1, 0, 0, 1, 1] n2487 := by
  exact checkExponentBoxTree_join c2488 c2511 (by decide +kernel)

private theorem c2529 : C ![4, 2, 1, 0, 1, 0, 0] ![8, 3, 1, 0, 1, 0, 1] n2529 := by
  decide +kernel

private theorem c2549 : C ![4, 2, 1, 0, 1, 1, 0] ![8, 3, 1, 0, 1, 1, 0] n2549 := by
  decide +kernel

private theorem c2560 : C ![4, 2, 1, 0, 1, 1, 1] ![8, 3, 1, 0, 1, 1, 1] n2560 := by
  decide +kernel

private theorem c2548 : C ![4, 2, 1, 0, 1, 1, 0] ![8, 3, 1, 0, 1, 1, 1] n2548 := by
  exact checkExponentBoxTree_join c2549 c2560 (by decide +kernel)

private theorem c2528 : C ![4, 2, 1, 0, 1, 0, 0] ![8, 3, 1, 0, 1, 1, 1] n2528 := by
  exact checkExponentBoxTree_join c2529 c2548 (by decide +kernel)

private theorem c2486 : C ![4, 2, 1, 0, 0, 0, 0] ![8, 3, 1, 0, 1, 1, 1] n2486 := by
  exact checkExponentBoxTree_join c2487 c2528 (by decide +kernel)

private theorem c2426 : C ![4, 2, 0, 0, 0, 0, 0] ![8, 3, 1, 0, 1, 1, 1] n2426 := by
  exact checkExponentBoxTree_join c2427 c2486 (by decide +kernel)

private theorem c2567 : C ![4, 4, 0, 0, 0, 0, 0] ![8, 7, 0, 0, 0, 1, 1] n2567 := by
  decide +kernel

private theorem c2576 : C ![4, 4, 0, 0, 1, 0, 0] ![8, 7, 0, 0, 1, 1, 1] n2576 := by
  decide +kernel

private theorem c2566 : C ![4, 4, 0, 0, 0, 0, 0] ![8, 7, 0, 0, 1, 1, 1] n2566 := by
  exact checkExponentBoxTree_join c2567 c2576 (by decide +kernel)

private theorem c2587 : C ![4, 4, 1, 0, 0, 0, 0] ![8, 7, 1, 0, 0, 0, 1] n2587 := by
  decide +kernel

private theorem c2600 : C ![4, 4, 1, 0, 0, 1, 0] ![8, 7, 1, 0, 0, 1, 1] n2600 := by
  decide +kernel

private theorem c2586 : C ![4, 4, 1, 0, 0, 0, 0] ![8, 7, 1, 0, 0, 1, 1] n2586 := by
  exact checkExponentBoxTree_join c2587 c2600 (by decide +kernel)

private theorem c2608 : C ![4, 4, 1, 0, 1, 0, 0] ![8, 7, 1, 0, 1, 0, 1] n2608 := by
  decide +kernel

private theorem c2618 : C ![4, 4, 1, 0, 1, 1, 0] ![8, 7, 1, 0, 1, 1, 0] n2618 := by
  decide +kernel

private theorem c2621 : C ![4, 4, 1, 0, 1, 1, 1] ![8, 7, 1, 0, 1, 1, 1] n2621 := by
  decide +kernel

private theorem c2617 : C ![4, 4, 1, 0, 1, 1, 0] ![8, 7, 1, 0, 1, 1, 1] n2617 := by
  exact checkExponentBoxTree_join c2618 c2621 (by decide +kernel)

private theorem c2607 : C ![4, 4, 1, 0, 1, 0, 0] ![8, 7, 1, 0, 1, 1, 1] n2607 := by
  exact checkExponentBoxTree_join c2608 c2617 (by decide +kernel)

private theorem c2585 : C ![4, 4, 1, 0, 0, 0, 0] ![8, 7, 1, 0, 1, 1, 1] n2585 := by
  exact checkExponentBoxTree_join c2586 c2607 (by decide +kernel)

private theorem c2565 : C ![4, 4, 0, 0, 0, 0, 0] ![8, 7, 1, 0, 1, 1, 1] n2565 := by
  exact checkExponentBoxTree_join c2566 c2585 (by decide +kernel)

private theorem c2425 : C ![4, 2, 0, 0, 0, 0, 0] ![8, 7, 1, 0, 1, 1, 1] n2425 := by
  exact checkExponentBoxTree_join c2426 c2565 (by decide +kernel)

/-- The complete binary certificate at this subtree root. -/
def certificate : MainTree := n2425

theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes lo hi certificate = true := c2425

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.Main06
