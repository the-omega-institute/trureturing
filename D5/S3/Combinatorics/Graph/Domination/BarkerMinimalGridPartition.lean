/- GID: D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition
   mirror-E: none(waiver:internal-stage-a)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.actualCount_quotient; premises=D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.row_certificate,D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.terminal_certificate,D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.initial_certificate
   digest: The total full-state partition intertwines the open-grid and quotient transfer orbits. -/

import D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridQuotient
import D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridTransfer
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridPartition

open scoped BigOperators

open D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridTransfer
open D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridQuotient

/-- The literal class of each of the 4672 full states. -/
private def classData : Array (Array (Fin 59)) :=
  #[
    #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 0, 5, 6, 7, 8, 6, 9, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 3, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 14, 5, 6, 7, 8, 6, 9, 8, 15, 16, 17, 18, 8, 19, 20, 21, 15, 0, 2, 0, 4, 0, 3, 0, 14, 11, 22, 12, 21, 22, 23, 21, 15, 16, 19, 18, 21, 17, 20, 8, 15, 24, 25, 26, 21, 25, 23, 21, 15],
    #[0, 0, 0, 0, 0, 0, 27, 28, 0, 0, 0, 0, 2, 3, 0, 0, 5, 6, 7, 8, 6, 9, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 32, 20, 8, 15, 33, 0, 0, 0, 34, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 37, 0, 38, 0, 0, 0, 0, 2, 0, 4, 0, 5, 6, 7, 8, 6, 0, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 39, 40, 41, 14, 0, 0, 0, 0, 42, 0, 0, 0, 5, 6, 7, 8, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 27, 0, 0, 0, 28, 29, 32, 31, 8, 30, 20, 21, 15, 5, 6, 7, 0, 6, 9, 8, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 33, 34, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 44, 45, 0, 0, 45, 46, 29, 32, 0, 0, 30, 20, 0, 0, 5, 6, 0, 0, 6, 9, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 32, 20, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 39, 0, 41, 0, 40, 0, 14, 29, 0, 31, 0, 30, 0, 21, 0, 5, 0, 7, 0, 6, 0, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[48, 49, 50, 8, 49, 9, 8, 15, 51, 0, 0, 0, 52, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 51, 52, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 14, 5, 6, 7, 8, 6, 9, 8, 15, 16, 17, 18, 8, 19, 20, 21, 15, 0, 2, 0, 4, 0, 3, 0, 14, 11, 22, 12, 21, 22, 23, 21, 15, 16, 19, 18, 21, 17, 20, 8, 15, 24, 25, 26, 21, 25, 23, 21, 15],
    #[0, 0, 0, 0, 0, 0, 27, 28, 0, 0, 0, 0, 2, 3, 0, 0, 5, 6, 7, 8, 6, 9, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 32, 20, 8, 15, 33, 0, 0, 0, 34, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 37, 0, 38, 0, 0, 0, 0, 2, 0, 4, 0, 5, 6, 7, 8, 6, 0, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 39, 40, 41, 14, 0, 0, 0, 0, 42, 0, 0, 0, 5, 6, 7, 8, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 27, 0, 0, 0, 28, 29, 32, 31, 8, 30, 20, 21, 15, 5, 6, 7, 0, 6, 9, 8, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 33, 34, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 44, 45, 0, 0, 45, 46, 29, 32, 0, 0, 30, 20, 0, 0, 5, 6, 0, 0, 6, 9, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 32, 20, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 39, 0, 41, 0, 40, 0, 14, 29, 0, 31, 0, 30, 0, 21, 0, 5, 0, 7, 0, 6, 0, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[48, 49, 50, 8, 49, 9, 8, 15, 51, 0, 0, 0, 52, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 51, 52, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 0, 5, 6, 7, 8, 6, 9, 8, 15, 10, 0, 0, 0, 54, 0, 0, 0, 0, 2, 0, 4, 0, 3, 0, 14, 11, 0, 12, 0, 22, 0, 21, 0, 16, 19, 18, 21, 17, 20, 8, 15, 55, 0, 0, 0, 56, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 27, 28, 0, 0, 0, 0, 2, 3, 0, 0, 5, 6, 7, 8, 6, 9, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 32, 20, 8, 15, 33, 0, 0, 0, 34, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 37, 0, 38, 0, 0, 0, 0, 2, 0, 4, 0, 5, 6, 7, 8, 6, 0, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 39, 40, 41, 14, 0, 0, 0, 0, 42, 0, 0, 0, 5, 6, 7, 8, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 27, 0, 0, 0, 28, 29, 32, 31, 0, 30, 20, 21, 0, 5, 6, 7, 0, 6, 9, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 44, 45, 0, 0, 45, 46, 29, 32, 0, 0, 30, 20, 0, 0, 5, 6, 0, 0, 6, 9, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 32, 20, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 39, 0, 41, 0, 40, 0, 14, 29, 0, 31, 0, 30, 0, 21, 0, 5, 0, 7, 0, 6, 0, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[48, 49, 50, 8, 49, 9, 8, 15, 51, 0, 0, 0, 52, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 51, 52, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 14, 5, 6, 7, 8, 6, 9, 8, 0, 16, 17, 18, 8, 0, 0, 0, 0, 0, 2, 0, 4, 0, 3, 0, 14, 11, 22, 12, 21, 22, 23, 21, 15, 16, 0, 18, 0, 17, 0, 8, 0, 57, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 27, 28, 0, 0, 0, 0, 2, 3, 0, 0, 5, 6, 7, 8, 6, 9, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 32, 20, 8, 15, 33, 0, 0, 0, 34, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 37, 0, 38, 0, 0, 0, 0, 2, 0, 4, 0, 5, 6, 7, 8, 6, 0, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 39, 40, 41, 14, 0, 0, 0, 0, 42, 0, 0, 0, 5, 6, 7, 8, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 27, 0, 0, 0, 28, 29, 32, 31, 8, 30, 20, 21, 15, 5, 6, 7, 0, 6, 9, 8, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 33, 34, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 44, 45, 0, 0, 45, 46, 29, 32, 0, 0, 30, 20, 0, 0, 5, 6, 0, 0, 6, 9, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 32, 20, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 39, 0, 41, 0, 40, 0, 14, 29, 0, 31, 0, 30, 0, 21, 0, 5, 0, 7, 0, 6, 0, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[48, 49, 50, 8, 49, 9, 8, 15, 51, 0, 0, 0, 52, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 51, 52, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 0, 5, 6, 7, 8, 6, 9, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 3, 0, 14, 11, 0, 12, 0, 22, 0, 21, 0, 16, 0, 18, 0, 17, 0, 8, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 27, 28, 0, 0, 0, 0, 2, 3, 0, 0, 5, 6, 7, 8, 6, 9, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 32, 20, 8, 15, 33, 0, 0, 0, 34, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 37, 0, 38, 0, 0, 0, 0, 2, 0, 4, 0, 5, 6, 7, 8, 6, 0, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 39, 40, 41, 14, 0, 0, 0, 0, 42, 0, 0, 0, 5, 6, 7, 8, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 27, 0, 0, 0, 28, 29, 32, 31, 0, 30, 20, 21, 0, 5, 6, 7, 0, 6, 9, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 44, 45, 0, 0, 45, 46, 29, 32, 0, 0, 30, 20, 0, 0, 5, 6, 0, 0, 6, 9, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 32, 20, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 39, 0, 41, 0, 40, 0, 14, 29, 0, 31, 0, 30, 0, 21, 0, 5, 0, 7, 0, 6, 0, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[48, 49, 50, 8, 49, 9, 8, 15, 51, 0, 0, 0, 52, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 51, 52, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 14, 5, 6, 7, 8, 6, 9, 8, 15, 16, 17, 18, 8, 19, 20, 21, 15, 0, 2, 0, 4, 0, 3, 0, 0, 11, 22, 12, 21, 0, 0, 0, 0, 10, 54, 0, 0, 0, 0, 0, 0, 55, 56, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 27, 28, 0, 0, 0, 0, 2, 3, 0, 0, 5, 6, 7, 8, 6, 9, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 32, 20, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 37, 0, 38, 0, 0, 0, 0, 2, 0, 4, 0, 5, 6, 7, 8, 6, 0, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 39, 40, 41, 14, 0, 0, 0, 0, 42, 0, 0, 0, 5, 6, 7, 8, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 27, 0, 0, 0, 28, 29, 32, 31, 8, 30, 20, 21, 15, 5, 6, 7, 0, 6, 9, 8, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 33, 34, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 44, 45, 0, 0, 45, 46, 29, 32, 0, 0, 30, 20, 0, 0, 5, 6, 0, 0, 6, 9, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 32, 20, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 39, 0, 41, 0, 40, 0, 14, 29, 0, 31, 0, 30, 0, 21, 0, 5, 0, 7, 0, 6, 0, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[48, 49, 50, 8, 49, 9, 8, 15, 51, 0, 0, 0, 52, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 51, 52, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 0, 5, 6, 7, 8, 6, 9, 8, 15, 10, 0, 0, 0, 54, 0, 0, 0, 0, 2, 0, 4, 0, 3, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 54, 0, 0, 0, 0, 0, 0, 58, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 27, 28, 0, 0, 0, 0, 2, 3, 0, 0, 5, 6, 7, 8, 6, 9, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 32, 20, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 37, 0, 38, 0, 0, 0, 0, 2, 0, 4, 0, 5, 6, 7, 8, 6, 0, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 39, 40, 41, 14, 0, 0, 0, 0, 42, 0, 0, 0, 5, 6, 7, 8, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 27, 0, 0, 0, 28, 29, 32, 31, 0, 30, 20, 21, 0, 5, 6, 7, 0, 6, 9, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 44, 45, 0, 0, 45, 46, 29, 32, 0, 0, 30, 20, 0, 0, 5, 6, 0, 0, 6, 9, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 32, 20, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 39, 0, 41, 0, 40, 0, 14, 29, 0, 31, 0, 30, 0, 21, 0, 5, 0, 7, 0, 6, 0, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[48, 49, 50, 8, 49, 9, 8, 15, 51, 0, 0, 0, 52, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 51, 52, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 14, 5, 6, 7, 8, 6, 9, 8, 0, 16, 17, 18, 8, 0, 0, 0, 0, 0, 2, 0, 4, 0, 3, 0, 0, 11, 22, 12, 21, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 27, 28, 0, 0, 0, 0, 2, 3, 0, 0, 5, 6, 7, 8, 6, 9, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 32, 20, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 37, 0, 38, 0, 0, 0, 0, 2, 0, 4, 0, 5, 6, 7, 8, 6, 0, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 39, 40, 41, 14, 0, 0, 0, 0, 42, 0, 0, 0, 5, 6, 7, 8, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 27, 0, 0, 0, 28, 29, 32, 31, 8, 30, 20, 21, 15, 5, 6, 7, 0, 6, 9, 8, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 33, 34, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 44, 45, 0, 0, 45, 46, 29, 32, 0, 0, 30, 20, 0, 0, 5, 6, 0, 0, 6, 9, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 32, 20, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 39, 0, 41, 0, 40, 0, 14, 29, 0, 31, 0, 30, 0, 21, 0, 5, 0, 7, 0, 6, 0, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[48, 49, 50, 8, 49, 9, 8, 15, 51, 0, 0, 0, 52, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 51, 52, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 0, 5, 6, 7, 8, 6, 9, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 3, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 27, 28, 0, 0, 0, 0, 2, 3, 0, 0, 5, 6, 7, 8, 6, 9, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 32, 20, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 37, 0, 38, 0, 0, 0, 0, 2, 0, 4, 0, 5, 6, 7, 8, 6, 0, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 11, 0, 12, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 39, 40, 41, 14, 0, 0, 0, 0, 42, 0, 0, 0, 5, 6, 7, 8, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 29, 30, 31, 21, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 27, 0, 0, 0, 28, 29, 32, 31, 0, 30, 20, 21, 0, 5, 6, 7, 0, 6, 9, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 44, 45, 0, 0, 45, 46, 29, 32, 0, 0, 30, 20, 0, 0, 5, 6, 0, 0, 6, 9, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 29, 30, 0, 0, 32, 20, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[0, 39, 0, 41, 0, 40, 0, 14, 29, 0, 31, 0, 30, 0, 21, 0, 5, 0, 7, 0, 6, 0, 8, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    #[48, 49, 50, 8, 49, 9, 8, 15, 51, 0, 0, 0, 52, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 51, 52, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0]]

/-- Every full state, including every unreachable state, has its literal class. -/
def classOf (s : State) : Fin 59 := (classData.getD (s.val / 64) #[]).getD (s.val % 64) 0

/-- The class of every accepted real-mask successor, with multiplicity one per mask. -/
def successors (s : State) : List (Fin 59) :=
  ((List.finRange 8).filter fun m => accepts (window s ⟨m.val, by omega⟩)).map
    fun m => classOf (append s m)

/-- Expanded quotient rows retain their nonnegative integer edge multiplicities. -/
def quotientSuccessors (i : Fin 59) : List (Fin 59) :=
  (rows i).flatMap fun e => List.replicate e.2.toNat e.1

private def Page (p : Fin 73) : Prop := ∀ r : Fin 64,
  let s : State := ⟨64 * p.val + r.val, by omega⟩
  List.Perm (successors s) (quotientSuccessors (classOf s)) ∧
    BarkerMinimalGridTransfer.terminal s = BarkerMinimalGridQuotient.terminal (classOf s)

private instance pageDecidable (p : Fin 73) : Decidable (Page p) := by
  unfold Page
  infer_instance

private theorem page_0 : Page 0 := by decide +kernel

private theorem page_1 : Page 1 := by decide +kernel

private theorem page_2 : Page 2 := by decide +kernel

private theorem page_3 : Page 3 := by decide +kernel

private theorem page_4 : Page 4 := by decide +kernel

private theorem page_5 : Page 5 := by decide +kernel

private theorem page_6 : Page 6 := by decide +kernel

private theorem page_7 : Page 7 := by decide +kernel

private theorem page_8 : Page 8 := by decide +kernel

private theorem page_9 : Page 9 := by decide +kernel

private theorem page_10 : Page 10 := by decide +kernel

private theorem page_11 : Page 11 := by decide +kernel

private theorem page_12 : Page 12 := by decide +kernel

private theorem page_13 : Page 13 := by decide +kernel

private theorem page_14 : Page 14 := by decide +kernel

private theorem page_15 : Page 15 := by decide +kernel

private theorem page_16 : Page 16 := by decide +kernel

private theorem page_17 : Page 17 := by decide +kernel

private theorem page_18 : Page 18 := by decide +kernel

private theorem page_19 : Page 19 := by decide +kernel

private theorem page_20 : Page 20 := by decide +kernel

private theorem page_21 : Page 21 := by decide +kernel

private theorem page_22 : Page 22 := by decide +kernel

private theorem page_23 : Page 23 := by decide +kernel

private theorem page_24 : Page 24 := by decide +kernel

private theorem page_25 : Page 25 := by decide +kernel

private theorem page_26 : Page 26 := by decide +kernel

private theorem page_27 : Page 27 := by decide +kernel

private theorem page_28 : Page 28 := by decide +kernel

private theorem page_29 : Page 29 := by decide +kernel

private theorem page_30 : Page 30 := by decide +kernel

private theorem page_31 : Page 31 := by decide +kernel

private theorem page_32 : Page 32 := by decide +kernel

private theorem page_33 : Page 33 := by decide +kernel

private theorem page_34 : Page 34 := by decide +kernel

private theorem page_35 : Page 35 := by decide +kernel

private theorem page_36 : Page 36 := by decide +kernel

private theorem page_37 : Page 37 := by decide +kernel

private theorem page_38 : Page 38 := by decide +kernel

private theorem page_39 : Page 39 := by decide +kernel

private theorem page_40 : Page 40 := by decide +kernel

private theorem page_41 : Page 41 := by decide +kernel

private theorem page_42 : Page 42 := by decide +kernel

private theorem page_43 : Page 43 := by decide +kernel

private theorem page_44 : Page 44 := by decide +kernel

private theorem page_45 : Page 45 := by decide +kernel

private theorem page_46 : Page 46 := by decide +kernel

private theorem page_47 : Page 47 := by decide +kernel

private theorem page_48 : Page 48 := by decide +kernel

private theorem page_49 : Page 49 := by decide +kernel

private theorem page_50 : Page 50 := by decide +kernel

private theorem page_51 : Page 51 := by decide +kernel

private theorem page_52 : Page 52 := by decide +kernel

private theorem page_53 : Page 53 := by decide +kernel

private theorem page_54 : Page 54 := by decide +kernel

private theorem page_55 : Page 55 := by decide +kernel

private theorem page_56 : Page 56 := by decide +kernel

private theorem page_57 : Page 57 := by decide +kernel

private theorem page_58 : Page 58 := by decide +kernel

private theorem page_59 : Page 59 := by decide +kernel

private theorem page_60 : Page 60 := by decide +kernel

private theorem page_61 : Page 61 := by decide +kernel

private theorem page_62 : Page 62 := by decide +kernel

private theorem page_63 : Page 63 := by decide +kernel

private theorem page_64 : Page 64 := by decide +kernel

private theorem page_65 : Page 65 := by decide +kernel

private theorem page_66 : Page 66 := by decide +kernel

private theorem page_67 : Page 67 := by decide +kernel

private theorem page_68 : Page 68 := by decide +kernel

private theorem page_69 : Page 69 := by decide +kernel

private theorem page_70 : Page 70 := by decide +kernel

private theorem page_71 : Page 71 := by decide +kernel

private theorem page_72 : Page 72 := by decide +kernel

private theorem pages (p : Fin 73) : Page p := by
  fin_cases p
  · exact page_0
  · exact page_1
  · exact page_2
  · exact page_3
  · exact page_4
  · exact page_5
  · exact page_6
  · exact page_7
  · exact page_8
  · exact page_9
  · exact page_10
  · exact page_11
  · exact page_12
  · exact page_13
  · exact page_14
  · exact page_15
  · exact page_16
  · exact page_17
  · exact page_18
  · exact page_19
  · exact page_20
  · exact page_21
  · exact page_22
  · exact page_23
  · exact page_24
  · exact page_25
  · exact page_26
  · exact page_27
  · exact page_28
  · exact page_29
  · exact page_30
  · exact page_31
  · exact page_32
  · exact page_33
  · exact page_34
  · exact page_35
  · exact page_36
  · exact page_37
  · exact page_38
  · exact page_39
  · exact page_40
  · exact page_41
  · exact page_42
  · exact page_43
  · exact page_44
  · exact page_45
  · exact page_46
  · exact page_47
  · exact page_48
  · exact page_49
  · exact page_50
  · exact page_51
  · exact page_52
  · exact page_53
  · exact page_54
  · exact page_55
  · exact page_56
  · exact page_57
  · exact page_58
  · exact page_59
  · exact page_60
  · exact page_61
  · exact page_62
  · exact page_63
  · exact page_64
  · exact page_65
  · exact page_66
  · exact page_67
  · exact page_68
  · exact page_69
  · exact page_70
  · exact page_71
  · exact page_72

/-- Every accepted successor in every full state belongs to exactly its specified
quotient row, with every multiplicity retained. -/
theorem row_certificate (s : State) : List.Perm (successors s) (quotientSuccessors (classOf s)) := by
  have h := pages ⟨s.val / 64, by omega⟩ ⟨s.val % 64, by omega⟩
  have hs : (⟨64 * (s.val / 64) + s.val % 64, by omega⟩ : State) = s := by
    apply Fin.ext
    dsimp
    omega
  simpa only [hs] using h.1

/-- Terminal weights agree on every full state, without a reachability premise. -/
theorem terminal_certificate (s : State) :
    BarkerMinimalGridTransfer.terminal s = BarkerMinimalGridQuotient.terminal (classOf s) := by
  have h := pages ⟨s.val / 64, by omega⟩ ⟨s.val % 64, by omega⟩
  have hs : (⟨64 * (s.val / 64) + s.val % 64, by omega⟩ : State) = s := by
    apply Fin.ext
    dsimp
    omega
  simpa only [hs] using h.2

/-- The exact initial class multiplicities of all 64 two-column starts. -/
def alpha : Vector := ![45, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All 64 labelled initial pairs, with no symmetry identifications. -/
def initialClasses : List (Fin 59) :=
  (List.finRange 64).map fun s => classOf ⟨s.val, by omega⟩

/-- The initial quotient row expanded with its full multiplicities. -/
def alphaClasses : List (Fin 59) :=
  (List.finRange 59).flatMap fun i => List.replicate (alpha i).toNat i

/-- The full initial row maps exactly to alpha. -/
theorem initial_certificate : List.Perm initialClasses alphaClasses := by decide +kernel
end D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridPartition
