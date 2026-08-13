using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class DensePhaseUnrealizableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed points cannot have positive exponential density at all large listing sizes.",
        H("Dense Phase Is Unrealizable"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-point-dense-phase-eventually-unrealizable"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/DensePhaseUnrealizable.fixed_point_dense_phase_eventually_unrealizable"),
                H("Positive fixed-point density is eventually unrealizable"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Y"), Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Finite")), Open, F.Id("Y"), Close,
                    CloseBracket, Comma, Esc,
                    Forall, Sp, F.Id("f"), Colon, Sp, F.Id("Y"), To, Sp, F.Id("Y"), Comma, Esc,
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("n"), Sp, Ge, Sp, D(2), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("Y"), Close,
                    Sp, Eq, Sp, F.Id("n"), Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("c"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Open, D(0), Sp, Lt, Sp, F.Id("c"), Sp, Land, Sp,
                    F.Id("c"), Sp, Lt, Sp, D(1), Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("Fix")), Open, F.Id("f"), Close, Close,
                    Sp, Le, Sp, F.Id("n"), Sp, Land, Sp,
                    Exists, Sp, new Formula.Subscript(F.Id("A"), D(0)),
                    InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Forall, Sp, F.Id("A"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    new Formula.Subscript(F.Id("A"), D(0)), Sp, Le, Sp, F.Id("A"),
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("Fix")), Open, F.Id("f"), Close, Close,
                    Sp, Neq, Sp, F.Id("c"), Sp, F.Id("n"), Caret, Grp(F.Id("A")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite output type Y with cardinality n at least two, the fixed "
                        + "points of f form a subtype of Y, so their cardinality is at most n. "
                        + "For each real c strictly between zero and one, powers n^A eventually "
                        + "exceed n/c, forcing c n^A above n.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Finite.card_subtype_le and "
                        + "tendsto_pow_atTop_atTop_of_one_lt. The proof combines the structural "
                        + "fixed-point bound with exponential divergence to obtain one threshold "
                        + "A0 that excludes the dense-phase equation for every A at least A0.")),
                    Paragraph(Text(
                        "This formalizes only clause (v) of the revised occurrence of source "
                        + "corollary 3.6: the dense phase is unrealizable. It does not formalize "
                        + "the older occurrence's distinct decay identity, and it does not by "
                        + "itself close the multi-clause corollary atom."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Diagonal/EscapeCount"))]));
}
