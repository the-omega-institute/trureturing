using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualSpectralMixtureUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite density mixtures satisfy the spectral SLD information upper bound.",
        H("Signed amplitude mixtures"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-spectral-mixture-upper"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ActualSpectralMixtureUpper.actual_spectral_mixture_upper"),
                H("Pointwise extended convexity"), StatementSource.FromAuthor(UpperFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/alipour2015extended")),
                Blocks(
                    Paragraph(Text("Both n and J are arbitrary finite types, with Fintype instances and DecidableEq n; neither is required to be nonempty. Every derivative and DifferentiableAt below is over the real field. The two positive neighborhood radii may differ. PSD means positive semidefinite, tr is the complex matrix trace, and scalar multiplication of matrices is used in the definition and derivative of M. The prime denotes the actual deriv at t. Q(A,B;h) denotes the existing spectralQFI A B h from ActualPureQubitGeometry, with its support-safe zero-denominator convention. Here h_r(i) is the component positivity proof at t extracted from the neighborhood premise. The displayed witness h_M is the mixture positivity proof used by Q.")),
                    Paragraph(Text("The conclusion supplies positivity and trace one for M(t), differentiability of M at t, its exact derivative, and the upper bound for the existing support-safe spectralQFI of that actual derivative. Zero amplitudes may have arbitrary derivatives. Singular states, changing ranks, noncommuting components and degenerate finite types remain in the quantified domain.")),
                    Paragraph(Text("The proof constructs Hermitian SLDs at the point from two-sided positivity. For the derivative B of a positive matrix curve A, its compression from ker A(t) to ker A(t) vanishes: the quadratic form of B is zero on kernel vectors, and polarization gives every kernel-to-kernel entry zero. This does not assert that B annihilates the kernel; support/kernel coherences may remain, including at rank-changing points. A positive weighted matrix-square estimate compares the mixture SLD with the component SLDs and amplitude derivatives. The trace of each component derivative is zero, which removes the corresponding cross terms. No amplitude is divided by its value.")),
                    Paragraph(Text("This repository-derived auxiliary addresses the upper inequality associated with equation 215.17 of CSAQ theorem 215.3. Extended convexity itself is established literature: Alipour and Rezakhani, Quantum Metrology: Extended Convexity of Quantum Fisher Information, equation (4), as recorded in Library/Quantum/alipour2015extended.md. With positive weights g_i squared, the classical Fisher term equals four times the sum of squared amplitude derivatives. The present statement instead explicitly permits signed amplitudes and zero amplitudes with arbitrary derivatives; it does not identify that amplitude term with the pointwise classical Fisher term at a zero weight, or replace the pointwise spectral value by a continuous Bures extension. No literature novelty is claimed. The source's cubic amplitude zeros additionally have zero amplitude derivative; that source-specific condition is not assumed here. This auxiliary supplies no lower measurement bound, common processor construction, exact sharp set, minimum dimension, curvature limit or rank repair, and claims no full theorem 215.3 coverage. Continuously differentiable and analytic source curves imply the pointwise differentiability premises; their source-specific amplitude normalization and common-space construction remain separate obligations.")))))));

    private static Formula UpperFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")),
            Amp, Forall, Sp, F.Id("n"), Comma, F.Id("J"), Esc, Mathrm, Grp(F.Id("finite")), Comma,
            Esc, Rho, Colon, F.Id("J"), To, Mathbb, Grp(F.Id("R")), To,
            Mathbb, Grp(F.Id("C")), Caret, Grp(F.Id("n"), Times, Sp, F.Id("n")), Comma,
            Esc, F.Id("g"), Colon, F.Id("J"), To, Mathbb, Grp(F.Id("R")), To, Mathbb, Grp(F.Id("R")),
            Comma, Esc, F.Id("t"), InMacro, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
            Amp, Open, Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("J"), Comma,
            Operatorname, Grp(F.Id("DifferentiableAt")), Open, Rho, Underscore, F.Id("i"), Comma, F.Id("t"), Close,
            Land, Operatorname, Grp(F.Id("DifferentiableAt")), Open, F.Id("g"), Underscore, F.Id("i"), Comma, F.Id("t"), Close, Close, RowBreak,
            Amp, Land, Open, Exists, Sp, DeltaLower, Underscore, F.Id("r"), Gt, D(0), Comma,
            Forall, Sp, F.Id("u"), InMacro, Mathbb, Grp(F.Id("R")), Comma,
            Bar, F.Id("u"), Minus, F.Id("t"), Bar, Lt, DeltaLower, Underscore, F.Id("r"), Longrightarrow,
            Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("J"), Comma,
            Operatorname, Grp(F.Id("PSD")), Open, Rho, Underscore, F.Id("i"), Open, F.Id("u"), Close, Close,
            Land, Operatorname, Grp(F.Id("tr")), Open, Rho, Underscore, F.Id("i"), Open, F.Id("u"), Close, Close, Eq, D(1), Close, RowBreak,
            Amp, Land, Open, Exists, Sp, DeltaLower, Underscore, F.Id("g"), Gt, D(0), Comma,
            Forall, Sp, F.Id("u"), InMacro, Mathbb, Grp(F.Id("R")), Comma,
            Bar, F.Id("u"), Minus, F.Id("t"), Bar, Lt, DeltaLower, Underscore, F.Id("g"), Longrightarrow,
            Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("J")), F.Id("g"), Underscore, F.Id("i"), Open, F.Id("u"), Close, Caret, D(2), Eq, D(1), Close, RowBreak,
            Amp, Longrightarrow, Quad, Mathrm, Grp(F.Id("let")), Esc,
            F.Id("M"), Open, F.Id("u"), Close, Eq, Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("J")),
            F.Id("g"), Underscore, F.Id("i"), Open, F.Id("u"), Close, Caret, D(2), Cdot,
            Rho, Underscore, F.Id("i"), Open, F.Id("u"), Close, Comma, RowBreak,
            Amp, Exists, Sp, F.Id("h"), Underscore, F.Id("M"), Colon,
            Operatorname, Grp(F.Id("PSD")), Open, F.Id("M"), Open, F.Id("t"), Close, Close, Comma,
            Operatorname, Grp(F.Id("tr")), Open, F.Id("M"), Open, F.Id("t"), Close, Close, Eq, D(1),
            Land, Operatorname, Grp(F.Id("DifferentiableAt")), Open, F.Id("M"), Comma, F.Id("t"), Close, RowBreak,
            Amp, Land, Sp, F.Id("M"), Apos, Open, F.Id("t"), Close, Eq,
            Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("J")), Open,
            D(2), F.Id("g"), Underscore, F.Id("i"), Open, F.Id("t"), Close,
            F.Id("g"), Underscore, F.Id("i"), Apos, Open, F.Id("t"), Close, Cdot,
            Rho, Underscore, F.Id("i"), Open, F.Id("t"), Close, Plus,
            F.Id("g"), Underscore, F.Id("i"), Open, F.Id("t"), Close, Caret, D(2), Cdot,
            Rho, Underscore, F.Id("i"), Apos, Open, F.Id("t"), Close, Close, RowBreak,
            Amp, Land, Sp, F.Id("Q"), Open, F.Id("M"), Open, F.Id("t"), Close, Comma,
            F.Id("M"), Apos, Open, F.Id("t"), Close, Semi, F.Id("h"), Underscore, F.Id("M"), Close, Le,
            Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("J")),
            F.Id("g"), Underscore, F.Id("i"), Open, F.Id("t"), Close, Caret, D(2),
            F.Id("Q"), Open, Rho, Underscore, F.Id("i"), Open, F.Id("t"), Close, Comma,
            Rho, Underscore, F.Id("i"), Apos, Open, F.Id("t"), Close, Semi,
            F.Id("h"), Underscore, F.Id("r"), Open, F.Id("i"), Close, Close, Plus,
            D(4), Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("J")),
            Open, F.Id("g"), Underscore, F.Id("i"), Apos, Open, F.Id("t"), Close, Close, Caret, D(2),
            End, Grp(F.Id("aligned"))));
}
