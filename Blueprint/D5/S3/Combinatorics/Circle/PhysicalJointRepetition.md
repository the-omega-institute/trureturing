# Explicit physical-J repetition at a fixed ear cut

## Theorem

Lean statement: `D5/S3/Combinatorics/Circle/PhysicalJointRepetition.physical_joint_repetition`.

For every `d >= 2`, `1 <= w <= 2^(d-1)-1`, `r >= 2`, and `cut <= d`, a supplied old physical order `tau` and its supplied joint order after inserting the fresh label at the same literal cut produce an explicit order at length `d*r` and its joint order at length `d*r+1`. The repeated word copies every physical occurrence in the descending block order `r-1,...,0`; the fresh label is inserted in the first block at the unchanged numeric cut.

The old row at block `j` is `G * a_i`, where `G = geom d r` and `a_i = actualSource d w i`. The augmented row is `2*G*a_i - F_j(i)`, with `F_j(i) = 2^i*w*geom d j + charge d w i`, `F_j(i) >= 0`, and `sum_i F_j(i) = w*2^(d*j)`. The top row is `R*g_i + H*a_i`, where `R = (2^d)^(r-1)`, `H = geom d (r-1)`, and `G = R+H`. The top augmented prefix is bounded directly from the supplied old and new prefixes; each lower row starts at `w*geom d (j+1)`, ends at `w*geom d j`, and stays in the new strip. Empty, complete, and overlong natural prefixes are included by `InStrip` and `inStrip_prefix`.

Equal numerical source values remain distinct physical labels. The result is a constructive charged triangular transport and does not prove unrestricted four-independent-gap `J` or Circle C3.1.

## Source

Repository-derived from `PeriodicShorteningArithmetic.periodic_source_equations`, `ThreeRowSource.repeated_source`, and `RunFirstEarTransport.earWord`.
