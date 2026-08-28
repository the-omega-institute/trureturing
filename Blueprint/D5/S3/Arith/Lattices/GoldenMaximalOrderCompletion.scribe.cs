using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class GoldenMaximalOrderCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Hodge lattice has a minimal golden-integer-stable completion of index two.",
        H("Golden Maximal-Order Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-maximal-order-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/GoldenMaximalOrderCompletion."
                        + "golden_maximal_order_completion"),
                H("The golden stable completion is minimal and has index two"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The lattice and ambient real space are the canonical concrete objects "
                            + "from ExactDualLatticeFormula. The endomorphism Phi is represented "
                            + "by one half of the identity plus the imported integral Hodge "
                            + "matrix, and Wmax is the sum of the original lattice with its Phi "
                            + "image.")),
                    Paragraph(Text(
                        "The first three clauses state literal containment, full real rank, and "
                            + "stability under every golden integer. A golden integer a has "
                            + "integral coordinates first(a) and second(a), and acts through the "
                            + "displayed integral linear combination of the identity and Phi.")),
                    Paragraph(Text(
                        "The fourth clause quantifies over every integral submodule containing the "
                            + "original lattice and preserved by all of those actions. It proves "
                            + "that Wmax is contained in each such candidate, which is the source's "
                            + "minimality assertion rather than a chosen-witness encoding.")),
                    Paragraph(Text(
                        "The final clauses compute two independent additive indices. The first is "
                            + "the relative index of the original lattice in Wmax; the second is "
                            + "the index of the range of the canonical ring embedding from the "
                            + "square-root order into GoldenInt. Both are exactly two.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the generic span, quotient, and subgroup-index "
                            + "infrastructure. The parity generator, concrete six-coordinate "
                            + "calculation, stability bridge, and both index computations are "
                            + "proved locally on the imported source carrier."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula ambient = F.Id("AmbientSpace");
        Formula lattice = F.Id("lattice");
        Formula maximal = F.Id("maximalLattice");
        Formula phi = F.Id("goldenOperator");
        Formula goldenInt = F.Id("GoldenInt");
        Formula completed = F.Id("completed");
        Formula a = F.Id("a");
        Formula completedType = Call("Submodule", integer, ambient);

        Formula Stability(Formula candidate) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("a"),
            goldenInt,
            Subset(
                Call("map", GoldenAction(a, phi), candidate),
                candidate));

        Formula minimality = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("completed"),
            completedType,
            Implies(
                And(Subset(lattice, completed), Stability(completed)),
                Subset(maximal, completed)));

        return Disp(new Formula.Aligned([
            Seq(Subset(lattice, maximal), Sp, Land),
            Seq(Equal(Call("span", real, maximal), Call("top", ambient)), Sp, Land),
            Seq(Stability(maximal), Sp, Land),
            Seq(minimality, Sp, Land),
            Seq(Equal(Call("relIndex", lattice, maximal), D(2)), Sp, Land),
            Seq(
                Equal(
                    Call("index", Call("range", F.Id("sqrtFiveOrderEmbedding"))),
                    D(2)),
                Dot),
        ]));
    }

    private static Formula GoldenAction(Formula a, Formula phi) =>
        Seq(
            Call("first", a), Sp, F.Id("id"), Sp, Plus, Sp,
            Call("second", a), Sp, phi);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(
            Seq(Operatorname, Grp(F.Id(name))),
            [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Subset(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);
}
