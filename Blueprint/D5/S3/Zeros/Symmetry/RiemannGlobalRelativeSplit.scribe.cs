using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class RiemannGlobalRelativeSplitDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical-line localization splits into global reflection closure and relative "
            + "coherence of the transverse zero support.",
        H("Global Reflection and Relative Coherence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("transverse-zero-support"),
                DeclarationHandle.Create(Prefix + "transverseSupport"),
                H("Transverse zero support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This set contains exactly the real displacements from one half of "
                        + "the nontrivial zeta zeros in the open critical strip."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("global-reflection-closure"),
                DeclarationHandle.Create(Prefix + "GlobalEvenRiemannHypothesis"),
                H("Global reflection closure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every displacement in the transverse support has its negative in "
                        + "the same support."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("one-observer-relative-coherence"),
                DeclarationHandle.Create(Prefix + "OneObserverRiemannHypothesis"),
                H("One-observer relative coherence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The transverse support is subsingleton, so any two nontrivial zeros "
                        + "have the same horizontal reading."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("riemann-global-relative-split"),
                DeclarationHandle.Create(
                    Prefix + "riemann_hypothesis_iff_global_even_and_one_observer"),
                H("Critical-line localization splits into two support laws"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Critical-line localization makes every transverse displacement "
                            + "zero, which proves both reflection closure and relative "
                            + "coherence.")),
                    Paragraph(Text(
                        "Conversely, reflection closure places both a displacement and "
                            + "its negative in the support. Relative coherence identifies "
                            + "them, forcing the displacement to vanish. The functional-"
                            + "equation reduction then covers every classical nontrivial "
                            + "zeta zero."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula support = F.Id("transverseSupport");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula reflectedClosure = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("d"), real)],
            new Formula.Logic(
                Member(d, support),
                FormulaLogicOperator.Implies,
                Member(Seq(Minus, d), support)));
        Formula relativeCoherence = Seq(
            Operatorname, Grp(F.Id("Subsingleton")), Open, support, Close);
        Formula right = new Formula.Logic(
            reflectedClosure,
            FormulaLogicOperator.And,
            relativeCoherence);
        Formula riemannHypothesis = Seq(
            Operatorname, Grp(F.Id("RiemannHypothesis")));

        return Disp(new Formula.Logic(
            riemannHypothesis,
            FormulaLogicOperator.Iff,
            right));
    }

    private static Formula Member(Formula element, Formula collection) =>
        Seq(element, Sp, InMacro, Sp, collection);
}
