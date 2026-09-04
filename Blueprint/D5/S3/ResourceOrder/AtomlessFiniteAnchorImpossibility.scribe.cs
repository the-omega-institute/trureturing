using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder;

internal sealed class AtomlessFiniteAnchorImpossibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite anchor families on null-singleton probability spaces admit implementations that pass every exposed test while being wrong almost everywhere.",
        H("Atomless Finite Anchor Impossibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("atomless-finite-anchor-evasion"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/AtomlessFiniteAnchorImpossibility"
                    + ".atomless_finite_anchor_evasion"),
                H("Finite anchors permit almost-everywhere evasion"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("A"), Comma, Sp, F.Id("X"), Comma, Sp,
                    F.Id("mu"), Colon,
                    Operatorname, Grp(F.Id("Measure")), Open, F.Id("X"), Close,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")),
                    Open, F.Id("A"), Close, CloseBracket,
                    OpenBracket, Operatorname, Grp(F.Id("NullSingletonClass")),
                    Open, F.Id("mu"), Close, CloseBracket,
                    OpenBracket, Operatorname, Grp(F.Id("IsProbabilityMeasure")),
                    Open, F.Id("mu"), Close, CloseBracket,
                    Comma, Sp,
                    F.Id("S"), Colon, F.Id("A"), To,
                    Operatorname, Grp(F.Id("Finset")), Open, F.Id("X"), Close,
                    Comma, Sp, F.Id("t"), Colon, F.Id("X"), To,
                    Operatorname, Grp(F.Id("Bool")), Comma, Sp,
                    Exists, Sp, F.Id("p"), Colon, F.Id("X"), To,
                    Operatorname, Grp(F.Id("Bool")), Comma, Sp,
                    Open, Forall, Sp, F.Id("a"), Comma, Sp, F.Id("x"), Comma, Sp,
                    F.Id("x"), Sp, InMacro, Sp,
                    F.Id("S"), Open, F.Id("a"), Close, Sp, Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("x"), Close, Eq,
                    F.Id("t"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    F.Id("mu"), Open,
                    OpenBrace, F.Id("x"), Sp, Mid, Sp,
                    F.Id("p"), Open, F.Id("x"), Close, Neq, Sp,
                    F.Id("t"), Open, F.Id("x"), Close, CloseBrace,
                    Close, Eq, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take the union of all exposed finite suites. It is finite, hence "
                        + "countable, so Mathlib's Set.Countable.measure_zero makes it null "
                        + "under the null-singleton hypothesis.")),
                    Paragraph(Text(
                        "The witness agrees with the truth on that union and flips the Boolean "
                        + "truth off it. It passes every suite, and its error set is exactly the "
                        + "complement of a null set, whose probability is one.")),
                    Paragraph(Text(
                        "The source atom is an orphaned multi-clause fragment. This theorem "
                        + "formalizes its complete nonatomic information-theoretic core. It does "
                        + "not assert the fragment's undefined covering number or optimal anchor "
                        + "capacity, its random-family Chernoff estimate, or its conditional PRG "
                        + "interpretation.")),
                    Paragraph(Text(
                        "Repository searches found the finite coverage-and-evasion theorem and "
                        + "general countable nullity results, but no declaration combining passage "
                        + "of every supplied suite with an almost-everywhere error witness."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/ResourceOrder/FiniteAnchorCoverage")),
        ]));
}
