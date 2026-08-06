using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class UniversalHeatTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Midline/UniversalHeatTrace",
            "A genuine heat abscissa determines strict-side l2 behavior, resonance, and the half-density midline while leaving boundary convergence explicit."),
        H("The Universal Heat-Trace Midline"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("heat-coefficients-have-the-half-abscissa-boundary"),
                H("Heat coefficients have the half-abscissa boundary"),
                LeanTheorem("D5/S3/Midline/UniversalHeatTrace.heat_coefficient_mem_iff"),
                Disp(Seq(Operatorname, Grp(F.Id("MemLp")), Open, F.Id("a"), Mapsto, Sp, F.Id("e"), Caret, Grp(Minus, F.Id("sM"), Open, F.Id("a"), Close), Comma, D(2), Close, Leftrightarrow, Operatorname, Grp(F.Id("Summable")), Open, F.Id("a"), Mapsto, Sp, F.Id("e"), Caret, Grp(Minus, D(2), Re, Open, F.Id("s"), Close, F.Id("M"), Open, F.Id("a"), Close), Close, Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Boundary behavior is extracted from the genuine abscissa definition: it prescribes convergence for sigma greater than alpha and divergence for sigma less than alpha, but says nothing at sigma equal to alpha. The flat iff in atom (i) implicitly assumes the separately named boundary-divergent convention. Squaring coordinate norms doubles the real parameter; the general theorem gives the exact summability criterion and the two strict-side implications.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("norm-square-is-the-vertical-invariant-heat-trace"),
                H("Norm square is the vertical-invariant heat trace"),
                LeanTheorem("D5/S3/Midline/UniversalHeatTrace.heat_vector_norm_sq"),
                Disp(Seq(Begin, Grp(F.Id("gathered")), Sp, F.Id("A"), Esc, F.Text, Grp(F.Id("countable")), Comma, Esc, D(0), InMacro, Sp, F.Id("A"), Comma, Esc, F.Id("M"), Open, D(0), Close, Eq, D(0), Comma, Esc, Open, Forall, Sp, F.Id("a"), Comma, Esc, D(0), Le, Sp, F.Id("M"), Open, F.Id("a"), Close, Close, Comma, Esc, Open, Exists, Sp, F.Id("a"), Comma, Esc, F.Id("M"), Open, F.Id("a"), Close, Neq, D(0), Close, Comma, RowBreak, Sp, Forall, Rho, InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc, Operatorname, Grp(F.Id("Summable")), Open, F.Id("a"), Mapsto, Sp, F.Id("e"), Caret, Grp(Minus, Rho, Sp, F.Id("M"), Open, F.Id("a"), Close), Close, Leftrightarrow, Alpha, Lt, Rho, Comma, Quad, Sp, Frac, Grp(Alpha), Grp(D(2)), Lt, SigmaLower, RowBreak, Sp, Rightarrow, Quad, Sp, Left, Vert, Mathbf, Grp(F.Id("Z")), Underscore, Grp(F.Id("M")), Open, SigmaLower, Plus, F.Id("it"), Close, Right, Vert, Caret, Grp(D(2)), Eq, F.Id("D"), Underscore, F.Id("M"), Open, D(2), SigmaLower, Close, Eq, Sum, Underscore, Grp(F.Id("a"), InMacro, Sp, F.Id("A")), F.Id("e"), Caret, Grp(Minus, D(2), SigmaLower, Sp, F.Id("M"), Open, F.Id("a"), Close), Dot, Sp, End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every vertical parameter t, the squared lp norm is the same heat trace at twice sigma. Thus imaginary translation changes phases but not the norm.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-source-pairing-is-the-heat-kernel"),
                H("The source pairing is the heat kernel"),
                LeanTheorem("D5/S3/Midline/UniversalHeatTrace.heat_vector_inner"),
                Disp(Seq(Begin, Grp(F.Id("gathered")), Sp, F.Id("A"), Esc, F.Text, Grp(F.Id("countable")), Comma, Esc, D(0), InMacro, Sp, F.Id("A"), Comma, Esc, F.Id("M"), Open, D(0), Close, Eq, D(0), Comma, Esc, Open, Forall, Sp, F.Id("a"), Comma, Esc, D(0), Le, Sp, F.Id("M"), Open, F.Id("a"), Close, Close, Comma, Esc, Open, Exists, Sp, F.Id("a"), Comma, Esc, F.Id("M"), Open, F.Id("a"), Close, Neq, D(0), Close, Comma, RowBreak, Sp, Forall, Rho, InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc, Operatorname, Grp(F.Id("Summable")), Open, F.Id("a"), Mapsto, Sp, F.Id("e"), Caret, Grp(Minus, Rho, Sp, F.Id("M"), Open, F.Id("a"), Close), Close, Leftrightarrow, Alpha, Lt, Rho, Comma, Quad, Sp, Frac, Grp(Alpha), Grp(D(2)), Lt, Re, Open, F.Id("s"), Close, Comma, Esc, Frac, Grp(Alpha), Grp(D(2)), Lt, Re, Open, F.Id("w"), Close, RowBreak, Sp, Rightarrow, Quad, Sp, Left, Langle, Mathbf, Grp(F.Id("Z")), Underscore, Grp(F.Id("M")), Open, F.Id("s"), Close, Comma, Mathbf, Grp(F.Id("Z")), Underscore, Grp(F.Id("M")), Open, F.Id("w"), Close, Right, Rangle, Eq, F.Id("D"), Underscore, F.Id("M"), Open, F.Id("s"), Plus, Overline, Grp(F.Id("w")), Close, Dot, Sp, End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The source-ordered inner product is the heat trace at s plus conjugate w. In this module resonance names the affine equation s plus conjugate w equals alpha; it does not assert meromorphic continuation or the existence of a pole.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("resonance-and-half-density-select-the-same-midline"),
                H("Resonance and half-density select the same midline"),
                LeanTheorem("D5/S3/Midline/UniversalHeatTrace.universal_heat_trace_midline"),
                Disp(Seq(Begin, Grp(F.Id("gathered")), Sp, Operatorname, Grp(F.Id("IsHeatAbscissa")), Open, F.Id("M"), Comma, Alpha, Close, RowBreak, Sp, Rightarrow, Sp, OpenBracket, Operatorname, Grp(F.Id("MemLp")), Open, Mathbf, Grp(F.Id("Z")), Underscore, Grp(F.Id("M")), Open, F.Id("s"), Close, Comma, D(2), Close, Leftrightarrow, Operatorname, Grp(F.Id("Summable")), Open, F.Id("a"), Mapsto, Sp, F.Id("e"), Caret, Grp(Minus, D(2), Re, Open, F.Id("s"), Close, F.Id("M"), Open, F.Id("a"), Close), Close, CloseBracket, Comma, RowBreak, Sp, OpenBracket, Re, Open, F.Id("s"), Close, Gt, Alpha, Slash, D(2), Rightarrow, Operatorname, Grp(F.Id("MemLp")), Open, Mathbf, Grp(F.Id("Z")), Underscore, Grp(F.Id("M")), Open, F.Id("s"), Close, Comma, D(2), Close, CloseBracket, Comma, Quad, OpenBracket, Re, Open, F.Id("s"), Close, Lt, Alpha, Slash, D(2), Rightarrow, Neg, Operatorname, Grp(F.Id("MemLp")), Open, Mathbf, Grp(F.Id("Z")), Underscore, Grp(F.Id("M")), Open, F.Id("s"), Close, Comma, D(2), Close, CloseBracket, Comma, RowBreak, Sp, OpenBracket, F.Id("s"), Plus, Overline, Grp(F.Id("s")), Eq, Alpha, Leftrightarrow, Re, Open, F.Id("s"), Close, Eq, Alpha, Slash, D(2), CloseBracket, Comma, Quad, OpenBracket, Open, Forall, Sp, F.Id("a"), Comma, Bar, F.Id("e"), Caret, Grp(Alpha, Sp, F.Id("M"), Open, F.Id("a"), Close, Slash, D(2)), F.Id("e"), Caret, Grp(Minus, F.Id("sM"), Open, F.Id("a"), Close), Bar, Eq, D(1), Close, Leftrightarrow, Re, Open, F.Id("s"), Close, Eq, Alpha, Slash, D(2), CloseBracket, Dot, Sp, End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The general theorem leaves equality at the boundary open. Self-resonance and coordinatewise unit modulus still select alpha over two and do not use boundary behavior. The companion resonance theorem also derives the unique partner w = alpha - conjugate s and proves that this partner map is an involution.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("boundary-divergence-restores-the-flat-iff"),
                H("Boundary divergence restores the flat iff"),
                LeanTheorem("D5/S3/Midline/UniversalHeatTrace.universal_heat_trace_midline_of_boundary_divergent"),
                Disp(Seq(Operatorname, Grp(F.Id("BoundaryDivergentAbscissa")), Open, F.Id("M"), Comma, Alpha, Close, Rightarrow, OpenBracket, Operatorname, Grp(F.Id("MemLp")), Open, Mathbf, Grp(F.Id("Z")), Underscore, Grp(F.Id("M")), Open, F.Id("s"), Close, Comma, D(2), Close, Leftrightarrow, Alpha, Slash, D(2), Lt, Re, Open, F.Id("s"), Close, CloseBracket, Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "This is the explicitly stronger class required by the original atom (i). Boundary behavior has not been folded into the genuine abscissa predicate; the strict flat iff is recovered only after boundary divergence is supplied.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("reflection-center-equals-the-abscissa"),
                H("Reflection center equals the abscissa"),
                LeanTheorem("D5/S3/Midline/UniversalHeatTrace.reflection_center_eq_abscissa_iff"),
                Disp(Seq(Forall, Alpha, Comma, F.Id("c"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Quad, Sp, Left, OpenBracket, Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, F.Id("s"), Eq, F.Id("c"), Minus, Overline, Grp(F.Id("s")), Leftrightarrow, Re, Open, F.Id("s"), Close, Eq, Frac, Grp(Alpha), Grp(D(2)), Right, CloseBracket, Leftrightarrow, Sp, F.Id("c"), Eq, Alpha, Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A separately supplied reflection s maps to c minus conjugate s has the universal heat-trace midline as its fixed line exactly when its center c is the heat-trace abscissa alpha.")))
            )),
[
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Midline/UniversalHeatTrace.heat_coefficient_mem_iff")),
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Midline/UniversalHeatTrace.heat_vector_inner")),
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Midline/UniversalHeatTrace.heat_vector_norm_sq")),
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Midline/UniversalHeatTrace.reflection_center_eq_abscissa_iff")),
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Midline/UniversalHeatTrace.universal_heat_trace_midline")),
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Midline/UniversalHeatTrace.universal_heat_trace_midline_of_boundary_divergent")),
                ]));
}
