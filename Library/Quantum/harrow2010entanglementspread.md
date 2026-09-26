---
bibkey: harrow2010entanglementspread
authors: Aram W. Harrow
year: 2010
title: Entanglement spread and clean resource inequalities
doi: 10.1142/9789814304634_0046
url: https://arxiv.org/abs/0909.1557v2
claim: Conditional disposal of different amounts of entanglement can decohere superposed protocols; clean execution needs appropriate communication or other resources.
strata_touched: []
license: citation-only
triage: anchor
---

# Entanglement spread and conditional coarse graining

## Primary source and locator

Proceedings of the XVIth International Congress on Mathematical Physics (2010), 536-540. The extended arXiv version is 0909.1557v2, revised 27 October 2013. Sections 1-2 of the parsed primary PDF describe conditional disposal and clean protocols. PDF page screenshots failed; no table or figure is used as evidence.

## Use and boundary

The general obstruction to coherently discarding branch-dependent entanglement is established literature. RT section 34 specializes it to flat sector encodings, computes the simultaneous multisector optimum, and constructs a scale semigroup. No priority for the general obstruction is claimed.

Uniform additional maximally entangled assistance leaves the rank-ratio bound unchanged in the specified integer-ratio family. Nonflat shared resources, communication and retained environments are outside that bound. The source's broader resource results are not all imported into the finite-code claim. The paper uses base-two quantities; the RT volume uses natural logarithms.

## Finite multisector optimization in the existing RT owner

The named RG section in `docs/develop/theory/ARITHMETIC_HOLOGRAPHIC_RT.md` concerns independent local CPTP maps that produce the exact target pure state on each basis sector. For source and target flat Schmidt ranks r_s and d_s, this requires positive integer ratios m_s=r_s/d_s. Local Stinespring dilations leave maximally entangled environmental records of ranks m_s. The bound on each record overlap is exp(-abs(log(m_s)-log(m_t))/2).

The RG proof constructs one nested family of environmental supports that attains every overlap simultaneously. For the distinct ordered values ell_i=log(m_i), define T=sum_i tanh((ell_(i+1)-ell_i)/4). The resulting global optimum over the stated class is the unhalved diamond error 2T/(1+T), including arbitrary passive references. The inverse of the exponential covariance matrix gives a common worst input and a joint projective measurement attaining the lower bound. This multisector optimization is not inferred merely from pairwise attainability. With m=(1,4,16), the exact error is 4/5, exceeding the largest pairwise bound 3/4.

For actual integer rank towers r_s(n)=b_s^n, optimal induced logical channels compose as an exponential dephasing semigroup in the scale difference. The continuous scale extension has a Lindblad generator built from threshold projections of log(b_s). Scale is not physical time, and only integer scales are used as finite Schmidt-rank encodings. This is a concrete consequence of the constructed maps; it is not a general gravitational renormalization statement.

These are written-mathematics results with finite checks. They are not attributed to Harrow's paper as explicit formulas, and no global novelty or Lean certification is claimed. Section 34's original proof uses the exact-basis-sector condition; the larger optimization is addressed separately by the following supplement, rather than silently changing the scope of that original argument.

## 2026-09-24: unrestricted-output and nonflat spectral supplement

Full written proof in the same PR: https://github.com/the-omega-institute/trureturing/pull/8890#issuecomment-5816839471 . The single theory owner remains `docs/develop/theory/ARITHMETIC_HOLOGRAPHIC_RT.md`; the comment is an explicit proposed continuation, not a claim that the main file has already been extended beyond section 35.

For each flagged source sector, require a flat target factor of rank d_s tensor a residual Schmidt probability spectrum lambda_s. Sort and zero-pad the spectra, put v_s=sqrt(lambda_s), and let K_st=v_s dot v_t. The supplement proves the exact infimum over all independent local CPTP maps, allowing erroneous, mixed, or wrong-sector outputs, is 2[1-min_{p in the probability simplex} p^T K p]. A projected-environment Ky Fan weak-majorization bound controls every competitor, including incorrect basis outputs. A reference-labelled input and ideal-output projection give the lower bound; simultaneous sorted Schmidt-basis splitting gives the matching Schur-channel upper bound. Shared classical randomness cannot improve the value, but communication and extra shared entanglement remain excluded.

For uniform residual spectra and positive integer rank ratios, this removes the exact-output restriction from the old 2T/(1+T) value. It does not solve the noninteger-ratio problem or arbitrary nonflat target spectra. For nonflat residuals, vanishing error is equivalent to uniform coalescence of the sorted square-root spectra. Equal residual von Neumann entropies do not suffice: spectra (1/2,1/8,1/8,1/8,1/8) and (1/4,1/4,1/4,1/4,0) both have entropy log 4 but have optimal error 1-5/(4 sqrt 2).

The general obstruction is Harrow's established background; the displayed spectral minimax formula and the unrestricted-output proof are the separately written PR result. A bounded primary-source search did not establish global priority. There is no new Lean declaration, Scribe proof claim, kernel validation, or gravitational RT resolution. The numerical checks are supporting falsification checks, not a replacement for the written proof.
