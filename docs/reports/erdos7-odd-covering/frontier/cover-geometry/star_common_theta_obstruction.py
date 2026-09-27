#!/usr/bin/env python3
"""Exact fixed-theta obstruction and layout-dependent positive witness."""
THETA_DENOMINATOR=2**24
STARS=((0, 1, 0, 1, 0, 1, 3, 14), (0, 2, 0, 2, 0, 2, 2, 13), (0, 3, 0, 3, 0, 3, 0, 16), (0, 3, 0, 3, 0, 3, 1, 18), (0, 3, 0, 3, 0, 3, 1, 15))
PAIR_CODES=(9, 11, 9, 9, 27, 18, 18, 27, 27, 27)
DUAL_NUMERATORS=(1607217, 154258, 4764971, 251967, 3466456, 1255757, 3320423, 1956167)
POSITIVE_THETA=(12812561, 12812561, 12812561, 12812561, 11171908, 12685072, 12685072, 12685072, 12685072, 16777216, 16777216, 16777216, 16777216, 16777216, 13074775, 13074775, 13074775, 11869034, 13074775, 13129121, 13129121, 13129121, 13129121, 16777216, 16777216, 16777216, 16777216, 16777216, 0, 0, 6620495, 7815823, 5190940, 11491235, 11491235, 11491235, 11491235, 16777216, 16777216, 16777216, 16777216, 16777216, 8828632, 8828632, 8828632, 8828632, 6290071, 8999146, 8999146, 8999146, 8999146, 8999146, 8126046, 8126046, 8999146, 8246238, 11188981, 11188981, 11188981, 11188981, 11188981, 7256297, 5169840, 7256297, 7256297, 7256297, 8999146, 8999146, 8999146, 8999146, 8999146, 6673541, 6673541, 7433390, 8126046, 9229821, 9229821, 9229821, 9229821, 9229821)
ANCHOR_SELECTORS=(
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 16, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 16, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 11, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 11, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 10, 11, 10, 7, 10, 1, 2, 1, 10, 11, 10, 7, 13, 1, 3, 1, 10, 11, 10, 7, 13, 1, 3, 1, 10, 4, 5, 4, 3, 1, 3, 1, 53, 48, 53, 34, 53, 1, 6, 6, 53, 48, 34, 34, 53, 1, 6, 6, 53, 48, 34, 34, 53, 1, 6, 6, 53, 15, 20, 20, 10, 1, 6, 6, 53, 48, 53, 34, 53, 1, 6, 6, 53, 48, 34, 34, 53, 1, 6, 6, 53, 48, 34, 34, 53, 1, 6, 6, 53, 15, 20, 20, 10, 1, 6, 6, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 0, 10, 11, 16, 7, 17, 1, 17, 1, 17, 11, 17, 7, 17, 1, 17, 1, 17, 11, 17, 7, 17, 1, 17, 1, 17, 4, 17, 4, 17, 1, 3, 1, 72, 48, 72, 34, 72, 1, 72, 6, 72, 48, 72, 34, 77, 1, 6, 6, 72, 48, 72, 34, 76, 1, 6, 6, 72, 15, 20, 20, 76, 1, 6, 6, 72, 48, 72, 34, 72, 1, 72, 6, 72, 48, 72, 34, 77, 1, 6, 6, 72, 48, 72, 34, 76, 1, 6, 6, 72, 15, 20, 20, 76, 1, 6, 6),
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 6, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 10, 11, 10, 11, 10, 11, 2, 2, 10, 11, 10, 8, 13, 11, 2, 2, 10, 11, 10, 8, 10, 11, 2, 2, 10, 11, 5, 5, 13, 1, 2, 2, 43, 48, 34, 34, 43, 48, 6, 6, 43, 48, 34, 34, 58, 48, 6, 6, 43, 48, 34, 34, 57, 48, 6, 6, 43, 48, 20, 20, 57, 6, 6, 6, 43, 48, 34, 34, 43, 48, 6, 6, 43, 48, 34, 34, 58, 48, 6, 6, 43, 48, 34, 34, 57, 48, 6, 6, 43, 48, 20, 20, 57, 6, 6, 6, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 10, 11, 10, 11, 17, 11, 17, 2, 10, 11, 10, 8, 17, 11, 17, 2, 10, 11, 10, 8, 17, 11, 17, 2, 17, 11, 17, 5, 17, 1, 17, 2, 43, 48, 34, 34, 77, 48, 6, 6, 78, 48, 34, 34, 77, 48, 6, 6, 76, 48, 34, 34, 76, 48, 6, 6, 76, 48, 20, 20, 76, 6, 6, 6, 43, 48, 34, 34, 77, 48, 6, 6, 78, 48, 34, 34, 77, 48, 6, 6, 76, 48, 34, 34, 76, 48, 6, 6, 76, 48, 20, 20, 76, 6, 6, 6),
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 2, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 10, 11, 8, 8, 10, 1, 2, 2, 10, 11, 8, 8, 13, 1, 2, 2, 10, 11, 8, 8, 13, 1, 2, 2, 13, 4, 5, 5, 3, 1, 3, 2, 53, 48, 34, 34, 53, 1, 6, 6, 53, 48, 34, 34, 53, 1, 6, 6, 53, 48, 34, 34, 53, 1, 6, 6, 53, 15, 20, 20, 10, 1, 6, 6, 53, 48, 34, 34, 53, 1, 6, 6, 53, 48, 34, 34, 53, 1, 6, 6, 53, 48, 34, 34, 53, 1, 6, 6, 53, 15, 20, 20, 10, 1, 6, 6, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 0, 10, 11, 8, 8, 17, 1, 2, 2, 17, 11, 8, 8, 17, 1, 2, 2, 17, 11, 8, 8, 17, 1, 2, 2, 17, 4, 5, 5, 17, 1, 3, 2, 53, 48, 34, 34, 53, 1, 6, 6, 53, 48, 34, 34, 77, 1, 6, 6, 53, 48, 34, 34, 76, 1, 6, 6, 53, 15, 20, 20, 76, 1, 6, 6, 53, 48, 34, 34, 53, 1, 6, 6, 53, 48, 34, 34, 77, 1, 6, 6, 53, 48, 34, 34, 76, 1, 6, 6, 53, 15, 20, 20, 76, 1, 6, 6),
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 2, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 10, 11, 10, 11, 10, 11, 2, 2, 10, 11, 8, 8, 13, 1, 2, 2, 10, 11, 10, 8, 10, 1, 2, 2, 10, 11, 5, 5, 3, 1, 3, 2, 53, 48, 53, 34, 53, 48, 6, 6, 53, 53, 34, 34, 53, 1, 6, 6, 53, 53, 34, 34, 53, 53, 6, 6, 53, 53, 20, 20, 53, 1, 6, 6, 53, 48, 53, 34, 53, 48, 6, 6, 53, 53, 34, 34, 53, 1, 6, 6, 53, 53, 34, 34, 53, 53, 6, 6, 53, 53, 20, 20, 53, 1, 6, 6, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 17, 15, 15, 15, 17, 15, 17, 2, 17, 15, 17, 8, 17, 15, 17, 2, 17, 15, 17, 8, 17, 15, 17, 2, 17, 15, 17, 5, 17, 1, 17, 2, 72, 67, 72, 34, 77, 67, 6, 6, 78, 67, 34, 34, 77, 67, 6, 6, 76, 67, 34, 34, 76, 67, 6, 6, 76, 67, 20, 20, 76, 1, 6, 6, 72, 67, 72, 34, 77, 67, 6, 6, 78, 67, 34, 34, 77, 67, 6, 6, 76, 67, 34, 34, 76, 67, 6, 6, 76, 67, 20, 20, 76, 1, 6, 6),
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 2, 7, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 2, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 10, 11, 10, 11, 13, 11, 2, 2, 10, 11, 8, 11, 13, 11, 2, 2, 10, 11, 8, 11, 13, 11, 2, 2, 13, 11, 5, 5, 13, 11, 3, 2, 53, 48, 53, 34, 53, 48, 6, 6, 53, 48, 34, 34, 53, 48, 6, 6, 53, 48, 34, 34, 53, 48, 6, 6, 53, 48, 20, 20, 57, 48, 6, 6, 53, 48, 53, 34, 53, 48, 6, 6, 53, 48, 34, 34, 53, 48, 6, 6, 53, 48, 34, 34, 53, 48, 6, 6, 53, 48, 20, 20, 57, 48, 6, 6, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 10, 11, 16, 11, 17, 11, 17, 2, 17, 11, 17, 11, 17, 11, 17, 2, 17, 11, 17, 11, 17, 11, 17, 2, 17, 11, 17, 5, 17, 11, 17, 2, 72, 48, 72, 34, 77, 48, 6, 6, 72, 48, 34, 34, 77, 48, 6, 6, 72, 48, 34, 34, 76, 48, 6, 6, 76, 48, 20, 20, 76, 48, 6, 6, 72, 48, 72, 34, 77, 48, 6, 6, 72, 48, 34, 34, 77, 48, 6, 6, 72, 48, 34, 34, 76, 48, 6, 6, 76, 48, 20, 20, 76, 48, 6, 6),
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 10, 11, 12, 7, 13, 11, 2, 1, 10, 11, 8, 7, 13, 1, 2, 1, 10, 11, 8, 7, 13, 1, 2, 1, 13, 4, 5, 4, 3, 1, 3, 1, 53, 48, 53, 34, 53, 48, 6, 6, 53, 53, 34, 34, 53, 1, 6, 6, 53, 53, 34, 34, 53, 1, 6, 6, 53, 15, 20, 20, 10, 1, 6, 6, 53, 48, 53, 34, 53, 48, 6, 6, 53, 53, 34, 34, 53, 1, 6, 6, 53, 53, 34, 34, 53, 1, 6, 6, 53, 15, 20, 20, 10, 1, 6, 6, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 0, 17, 11, 15, 7, 17, 11, 17, 1, 17, 11, 17, 7, 17, 1, 17, 1, 17, 11, 17, 7, 17, 1, 17, 1, 17, 4, 17, 4, 17, 1, 3, 1, 53, 48, 53, 34, 77, 48, 6, 6, 53, 53, 34, 34, 77, 1, 6, 6, 53, 53, 34, 34, 76, 1, 6, 6, 76, 15, 20, 20, 76, 1, 6, 6, 53, 48, 53, 34, 77, 48, 6, 6, 53, 53, 34, 34, 77, 1, 6, 6, 53, 53, 34, 34, 76, 1, 6, 6, 76, 15, 20, 20, 76, 1, 6, 6),
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 10, 11, 10, 7, 10, 11, 2, 1, 10, 11, 8, 7, 13, 1, 2, 1, 10, 11, 8, 7, 13, 1, 2, 1, 10, 4, 5, 4, 3, 1, 3, 1, 53, 53, 53, 34, 53, 53, 6, 6, 53, 53, 34, 34, 53, 1, 6, 6, 53, 53, 34, 34, 53, 1, 6, 6, 53, 15, 20, 20, 10, 1, 6, 6, 53, 53, 53, 34, 53, 53, 6, 6, 53, 53, 34, 34, 53, 1, 6, 6, 53, 53, 34, 34, 53, 1, 6, 6, 53, 15, 20, 20, 10, 1, 6, 6, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 0, 14, 11, 14, 7, 17, 11, 17, 1, 17, 11, 17, 7, 17, 1, 17, 1, 17, 11, 17, 7, 17, 1, 17, 1, 17, 4, 17, 4, 17, 1, 3, 1, 53, 53, 53, 34, 77, 53, 6, 6, 53, 53, 34, 34, 77, 1, 6, 6, 53, 53, 34, 34, 76, 1, 6, 6, 76, 15, 20, 20, 76, 1, 6, 6, 53, 53, 53, 34, 77, 53, 6, 6, 53, 53, 34, 34, 77, 1, 6, 6, 53, 53, 34, 34, 76, 1, 6, 6, 76, 15, 20, 20, 76, 1, 6, 6),
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 16, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 16, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 11, 5, 11, 11, 15, 5, 11, 11, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 10, 1, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 10, 11, 10, 7, 10, 11, 2, 1, 10, 11, 8, 7, 13, 1, 2, 1, 10, 11, 8, 7, 13, 1, 2, 1, 13, 4, 5, 4, 3, 1, 3, 1, 53, 48, 34, 34, 53, 48, 6, 6, 53, 48, 34, 34, 58, 1, 6, 6, 53, 48, 34, 34, 57, 1, 6, 6, 53, 15, 20, 20, 10, 1, 6, 6, 53, 48, 34, 34, 53, 48, 6, 6, 53, 48, 34, 34, 58, 1, 6, 6, 53, 48, 34, 34, 57, 1, 6, 6, 53, 15, 20, 20, 10, 1, 6, 6, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 0, 14, 11, 15, 7, 17, 11, 17, 1, 17, 11, 17, 7, 17, 1, 17, 1, 17, 11, 17, 7, 17, 1, 17, 1, 17, 4, 17, 4, 17, 1, 3, 1, 72, 48, 34, 34, 77, 48, 6, 6, 78, 48, 34, 34, 77, 1, 6, 6, 76, 48, 34, 34, 76, 1, 6, 6, 76, 15, 20, 20, 76, 1, 6, 6, 72, 48, 34, 34, 77, 48, 6, 6, 78, 48, 34, 34, 77, 1, 6, 6, 76, 48, 34, 34, 76, 1, 6, 6, 76, 15, 20, 20, 76, 1, 6, 6),
)
import argparse, importlib.util, json
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod
from pathlib import Path

PIN_JSON='2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f'
PIN_PRODUCER='fe0bff7dceec1f2435c91218f371a12b523bec062e91466ad6e6fafd4a21cce6'

class Checks:
    def __init__(self):self.values={};self.evaluations=0
    def require(self,name,p):
        self.evaluations+=1
        if not p:raise ArithmeticError(name)
        self.values[name]=True

def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x

def source(path,checks):
    raw=path.read_bytes();p=path.with_suffix('.py');pr=p.read_bytes()
    checks.require('pinned604_source',sha256(raw).hexdigest()==PIN_JSON and sha256(pr).hexdigest()==PIN_PRODUCER)
    d=json.loads(raw)
    spec=importlib.util.spec_from_file_location('source604',p);lib=importlib.util.module_from_spec(spec);spec.loader.exec_module(lib)
    cs=d['central_source'];w=list(map(F,cs['masses3']));v=list(map(F,cs['masses5']));d3=F(cs['density3']);d5=list(map(F,cs['density5_by_root']))
    L=list(map(F,d['complete_coefficients']['loss']));W=list(map(F,d['complete_coefficients']['weighted_nonunit_query']))
    c=F(d['constants']['continuation_c']);alpha=F(d['constants']['Haar_factor'])
    checks.require('same_source_coefficients',len(L)==len(W)==512 and min(L+W)>=0 and W[0]==0 and c==F(1084133,201247200) and alpha==F(2673,138320))
    cells=[(l,m) for l,m in product(range(6),range(20)) if w[l]*v[m]>0 and (l//3,m//5)!=(0,0)]
    checks.require('eighty_positive_unmasked_cells',len(cells)==80)
    groups=[];bid=[]
    for l,m in cells:
        key=(0 if l<3 else l-2,0 if m<5 else (2 if m//5==2 else 1))
        if key not in groups:groups.append(key)
        bid.append(groups.index(key))
    checks.require('eight_source_orbits',len(groups)==8 and [bid.count(i) for i in range(8)]==[30,12,5,10,4,5,10,4])
    selectors=[]
    for e3,e5 in product(range(4),repeat=2):
        rows=[];seen=set()
        for xs in lib.selectors(6,3,w,[d3/2]*2,e3):
            for ys in lib.selectors(20,5,v,[3*z/5 for z in d5],e5):
                dx,dy=dict(xs),dict(ys)
                row=tuple(dx.get(l,0)*dy.get(m,0) for l,m in cells)
                if row not in seen:seen.add(row);rows.append(row)
        selectors.append(rows)
    coef=[(1-c)*x+c*y for x,y in zip(L,W)]
    return lib,d,w,v,c,alpha,cells,groups,bid,selectors,coef

def grids(lib,cells,checks):
    roles=list(product(range(2),range(4),range(2),range(4)))
    H=[[F()]*80 for _ in range(32)];minimum_z=F(1);maximum_dis=F();minimum_b=F(1)
    for t,(l,m) in enumerate(cells):
        i,j=l//3,m//5;b=[]
        for q,st in zip(lib.OUTSIDE,STARS):
            r1,c1,pi,pj,r2,c2,l9,m25=st;r=F(1,q-1);a=F(1,q*(q-2))
            value=1-r*(int(i==r1)+int(j==c1)+int((i,j)==(pi,pj))+int(l==l9)+int(m==m25))-a*(int(i==r2)+int(j==c2))
            checks.require('all_star_factors_positive',value>0);b.append(value)
        beta=[]
        for e,(x,y) in enumerate(lib.EDGES):
            q,r=lib.OUTSIDE[x],lib.OUTSIDE[y]
            kappa=F(1,(q-1)*(r-1))+F(1,q*(q-2)*(r-1))+F(1,(q-1)*r*(r-2))
            R,C,I,J=roles[PAIR_CODES[e]]
            beta.append(kappa*(1+int(i==R)+int(j==C)+int((i,j)==(I,J))))
        u=[beta[e]/(b[x]*b[y]) for e,(x,y) in enumerate(lib.EDGES)]
        z=1-sum(u)+sum(u[e]*u[f] for e,f in lib.MATCHINGS)
        ds=max(sum(u[f] for f in range(10) if not lib.EDGE_MASKS[e]&lib.EDGE_MASKS[f]) for e in range(10))
        checks.require('all_eighty_cells_strict_shearer',z>0 and ds<1)
        minimum_z=min(minimum_z,z);maximum_dis=max(maximum_dis,ds);minimum_b=min(minimum_b,min(b))
        g=[prod(b[q] for q in range(5) if not T>>q&1) for T in range(32)]
        for T in range(32):
            value=g[T]-sum(beta[e]*g[T|lib.EDGE_MASKS[e]] for e in range(10) if not T&lib.EDGE_MASKS[e])
            value+=sum(beta[e]*beta[f]*g[T|lib.EDGE_MASKS[e]|lib.EDGE_MASKS[f]] for e,f in lib.MATCHINGS if not T&(lib.EDGE_MASKS[e]|lib.EDGE_MASKS[f]))
            checks.require('all_support_grids_nonnegative',value>=0);H[T][t]=value
    return H,dict(minimum_full_Z=minimum_z,maximum_disjoint_sum=maximum_dis,minimum_star_factor=minimum_b)

def actual_originals(lib,data,checks):
    roles=list(product(range(2),range(4),range(2),range(4)))
    rows=[]
    for rec in data['retained_inventory']:
        exps=rec['exponents'];parts=[];a,b=exps[:2]
        active=[i for i,z in enumerate(exps[2:]) if z]
        if rec['kind']=='central15':parts=[(15,0)]
        elif rec['kind']=='pair':
            edge=lib.EDGES.index(tuple(active));R,C,I,J=roles[PAIR_CODES[edge]]
            if a:parts.append((3,R if not b else I))
            if b:parts.append((5,C if not a else J))
            for qi in active:parts.append((lib.OUTSIDE[qi]**exps[qi+2],1))
        else:
            qi=active[0];q=lib.OUTSIDE[qi];r1,c1,I,J,r2,c2,l9,m25=STARS[qi]
            if a==b==1:parts.extend(((3,I),(5,J)));outside=3
            elif a==1:parts.append((3,r1 if exps[qi+2]==1 else r2));outside=1
            elif b==1:parts.append((5,c1 if exps[qi+2]==1 else c2));outside=2
            elif a==2:parts.append((9,l9//3+3*(l9%3)));outside=4
            elif b==2:parts.append((25,m25//5+5*(m25%5)));outside=5
            else:raise ArithmeticError('unexpected star inventory')
            parts.append((q**exps[qi+2],outside))
        modulus=prod(m for m,r in parts);residue=sum(r*(modulus//m)*pow(modulus//m,-1,m) for m,r in parts)%modulus
        checks.require('actual_crt_original',modulus==rec['modulus'] and all(residue%m==r%m for m,r in parts))
        rows.append(dict(modulus=modulus,residue=residue,kind=rec['kind'],parts=parts))
    checks.require('same156_distinct_odd_moduli',len(rows)==len({r['modulus'] for r in rows})==156 and all(r['modulus']%2==1 for r in rows))
    pure=list(data['central_source']['pure3'])+list(data['central_source']['pure5'])+[(q,0) for q in lib.OUTSIDE]
    checks.require('actual_pure_and_mixed_inventory_distinct',len({m for m,r in pure}|{r['modulus'] for r in rows})==169)
    return dict(pure=pure,mixed=rows,all_other_originals='absent; certificate bounds remain valid for all admitted arbitrary remaining phases/heights')

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',type=Path,default=Path(__file__).with_name('actual_pair_activation_certificate.json'));p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=p.parse_args();checks=Checks()
    lib,data,w,v,c,alpha,cells,groups,bid,S,coef=source(args.source,checks)
    H,region=grids(lib,cells,checks)
    mass=[w[l]*v[m]*H[0][i] for i,(l,m) in enumerate(cells)]
    queries=[(mode,T) for mode,T in product(range(16),range(32)) if coef[32*mode+T]>0]
    checks.require('511_complete_query_rows',len(queries)==511)
    matrices=[]
    for mode,T in queries:
        rows=[]
        for sel in S[mode]:
            row=[F()]*8
            for t,b in enumerate(bid):row[b]+=sel[t]*H[T][t]
            rows.append(row)
        matrices.append(rows)
    m8=[sum(mass[t] for t,b in enumerate(bid) if b==g) for g in range(8)]
    payoffs=[]
    for component in ANCHOR_SELECTORS:
        checks.require('complete_dual_selector_tuple',len(component)==511)
        vector=[(1-c)*x for x in m8]
        for index,(mode,T) in enumerate(queries):
            k=component[index];checks.require('dual_selector_is_actual_menu_entry',0<=k<len(S[mode]))
            vector=[x-coef[32*mode+T]*y for x,y in zip(vector,matrices[index][k])]
        payoffs.append(vector)
    weights=[F(n,THETA_DENOMINATOR) for n in DUAL_NUMERATORS]
    checks.require('dual_weights_form_probability',len(weights)==len(payoffs)==8 and min(weights)>0 and sum(weights)==1)
    upper=[sum(p*row[b] for p,row in zip(weights,payoffs)) for b in range(8)]
    for value in upper:checks.require('all_common_theta_payoffs_below_minus1over30000',value < -F(1,30000))
    theta=[F(n,THETA_DENOMINATOR) for n in POSITIVE_THETA]
    checks.require('positive_witness_theta_bounds',len(theta)==80 and min(theta)>=0 and max(theta)<=1)
    m=sum(x*y for x,y in zip(theta,mass));debit=F()
    for mode,T in queries:
        screen=max(sum(s*t*h for s,t,h in zip(sel,theta,H[T])) for sel in S[mode]);debit+=coef[32*mode+T]*screen
    gate=(1-c)*m-debit
    checks.require('layout_dependent_gate_above3over500',gate>F(3,500))
    checks.require('positive_witness_Haar_above1over8700',alpha*gate>F(1,8700))
    actual=actual_originals(lib,data,checks)
    out=dict(schema='star-common-theta-obstruction-v1',source=dict(file=args.source.name,json_sha256=PIN_JSON,producer_sha256=PIN_PRODUCER),
             scope=dict(fixed='604 pure3/pure5 source and central15=0',family='one globally fixed star/pair layout and its full finite source-preserving group orbit',negative='No layout-independent theta makes the fixed cap/screen gate positive on this orbit',positive='Each orbit layout has its transported layout-dependent theta with gate>3/500',excluded='No failure claimed for layout-dependent theta, stronger actual-source constructions or unrestricted Erdős#7',lean_verified=False),
             stars=STARS,pair_codes=PAIR_CODES,cells=cells,groups=groups,orbit_sizes=[bid.count(i) for i in range(8)],
             strict_region=region,selector_counts=[len(x) for x in S],query_ids=queries,
             dual=dict(denominator=THETA_DENOMINATOR,numerators=DUAL_NUMERATORS,selector_tuples=ANCHOR_SELECTORS,payoff_vectors=payoffs,combined_upper_vector=upper,uniform_negative_margin=F(1,30000)),
             positive=dict(denominator=THETA_DENOMINATOR,theta_numerators=POSITIVE_THETA,mass=m,weighted_debit=debit,gate=gate,Haar_lower=alpha*gate),
             actual_originals=actual,checks=checks.values,predicate_evaluations=checks.evaluations,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(out),indent=2)+'\n')
    print('PASS',len(checks.values),'predicates',checks.evaluations,'evaluations; negative margin',float(-max(upper)),'positive gate',float(gate),flush=True)
if __name__=='__main__':main()
