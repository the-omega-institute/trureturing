using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeHierarchy;

internal sealed class RefinementMatrixDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeHierarchy/RefinementMatrix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An ordered state enumeration makes every false refinement cell executable, "
            + "deterministic, and proof-backed.",
        H("Executable Refinement Matrix"),
        Blocks(
            Definition("kernel-comparison", "KernelComparison",
                "Kernel comparison cases",
                "The four cases distinguish equality, either strict direction, and "
                    + "incomparability."),
            Definition("classify-kernel-comparison", "kernelComparison",
                "Classified kernel comparison",
                "The two decidable inclusion cells determine the four-way classification."),
            Definition("refinement-witness", "refinementWitness",
                "Executable refinement witness",
                "Spec spelling refinementWitness?. The search uses states.product states, "
                    + "visiting the outer-left state first and the inner-right state second."),
            Theorem("refinement-witness-order", "refinementWitness_order",
                "The selector uses the documented pair order", WitnessOrder()),
            Theorem("refinement-witness-none-iff-included",
                "refinementWitness_eq_none_iff",
                "No witness exactly means refinement", WitnessNone()),
            Theorem("refinement-witness-some-is-sound",
                "refinementWitness_eq_some_implies",
                "A returned refinement witness is sound", WitnessSome()),
            Theorem("refinement-witness-exists-iff-not-refines",
                "refinementWitness_exists_iff_not_kernelRefines",
                "A false cell has a deterministic witness", WitnessExistsIff()),
            Theorem("kernel-comparison-spec", "kernelComparison_spec",
                "Kernel comparison carries all inclusion and witness payloads",
                ComparisonSpec()))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, string title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The certificate follows from executable ordered search and Boolean "
                    + "agreement reflection."))),
            DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Paren(Formula formula) => Seq(Open, formula, Close);

    private static Formula Catalog() => F.Id("C");
    private static Formula Enumeration() => F.Id("E");
    private static Formula LeftIndex() => F.Id("i");
    private static Formula RightIndex() => F.Id("j");
    private static Formula Pair() => F.Id("p");
    private static Formula Refines(Formula finer, Formula coarser) =>
        Call("KernelRefines", Catalog(), finer, coarser);
    private static Formula Witness(Formula finer, Formula coarser) =>
        Call("refinementWitness", Catalog(), Enumeration(), finer, coarser);
    private static Formula WitnessExists(Formula finer, Formula coarser) => Paren(Seq(
        Exists, Sp, Pair(), Comma, Sp, Witness(finer, coarser), Sp, Eq, Sp,
        Call("some", Pair())));
    private static Formula Comparison(Formula value) => Seq(
        Call("kernelComparison", Catalog(), LeftIndex(), RightIndex()),
        Sp, Eq, Sp, value);
    private static Formula Agrees(Formula index) =>
        Call("agrees", Call("primitives", Call("theoremAt", Catalog(), index)),
            Call("fst", Pair()), Call("snd", Pair()));

    private static Formula WitnessOrder() => Seq(
        Witness(LeftIndex(), RightIndex()), Sp, Eq, Sp,
        Call("find",
            Call("product", Call("states", Enumeration()), Call("states", Enumeration())),
            Call("separatesRefinement", Catalog(), LeftIndex(), RightIndex())));

    private static Formula WitnessNone() => Seq(
        Witness(LeftIndex(), RightIndex()), Sp, Eq, Sp, Call("none"),
        Sp, Leftrightarrow, Sp, Refines(LeftIndex(), RightIndex()));

    private static Formula WitnessSome() => Implies(
        Seq(Witness(LeftIndex(), RightIndex()), Sp, Eq, Sp, Call("some", Pair())),
        And(Agrees(LeftIndex()), Seq(Neg, Agrees(RightIndex()))));

    private static Formula WitnessExistsIff() => Seq(
        WitnessExists(LeftIndex(), RightIndex()), Sp, Leftrightarrow, Sp,
        Neg, Refines(LeftIndex(), RightIndex()));

    private static Formula ComparisonSpec()
    {
        Formula equal = Seq(Comparison(F.Id("equal")), Sp, Leftrightarrow, Sp,
            And(Refines(LeftIndex(), RightIndex()),
                Refines(RightIndex(), LeftIndex())));
        Formula finer = Seq(Comparison(F.Id("strictlyFiner")), Sp, Leftrightarrow, Sp,
            And(Refines(LeftIndex(), RightIndex()),
                WitnessExists(RightIndex(), LeftIndex())));
        Formula coarser = Seq(Comparison(F.Id("strictlyCoarser")), Sp,
            Leftrightarrow, Sp,
            And(WitnessExists(LeftIndex(), RightIndex()),
                Refines(RightIndex(), LeftIndex())));
        Formula incomparable = Seq(Comparison(F.Id("incomparable")), Sp,
            Leftrightarrow, Sp,
            And(WitnessExists(LeftIndex(), RightIndex()),
                WitnessExists(RightIndex(), LeftIndex())));
        return And(Paren(equal),
            And(Paren(finer), And(Paren(coarser), Paren(incomparable))));
    }
}
