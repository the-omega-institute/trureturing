using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenBranchObserverDecompositionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenBranchObserverDecomposition."
            + "golden_branch_observer_decomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden branch conjugation splits the two-dimensional observation space into "
            + "trivial and sign channels.",
        H("Golden Branch Observer Decomposition"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-branch-observer-decomposition"),
            DeclarationHandle.Create(Declaration),
            H("The two golden branches are the trivial and sign representations"),
            StatementSource.FromAuthor(DecompositionFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier is the complex coordinate space on the two real golden "
                        + "embeddings. Galois conjugation is the canonical bit flip, and the "
                        + "even and odd maps are the half-sum and half-difference projectors.")),
                Paragraph(Text(
                    "The proof applies the repository's general involution decomposition, "
                        + "then computes the two projector ranges as the spans of (1,1) and "
                        + "(1,-1). These spans are complementary; conjugation acts on them "
                        + "with eigenvalues one and minus one."))),
            DescribeRole.Theorem))));

    private static Formula DecompositionFormula()
    {
        Formula j = F.Id("J");
        Formula identity = F.Id("I");
        Formula even = Subscript("P", F.Id("ev"));
        Formula odd = Subscript("P", F.Id("odd"));
        Formula ePlus = Subscript("e", Plus);
        Formula eMinus = Subscript("e", Minus);
        Formula v = F.Id("v");
        Formula branchSpace = Subscript("V", F.Id("br"));
        Formula evenChannel = Subscript("V", F.Id("ev"));
        Formula oddChannel = Subscript("V", F.Id("odd"));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula half = new Formula.Fraction(D(1), D(2));

        Formula decomposition = ForAll(
            "v",
            branchSpace,
            All(
                Equal(v, Add(Apply(even, v), Apply(odd, v))),
                Equal(Call("J", Apply(even, v)), Apply(even, v)),
                Equal(Call("J", Apply(odd, v)), Neg(Apply(odd, v)))));
        Formula evenEigen = ForAll(
            "v",
            evenChannel,
            Equal(Call("J", v), v));
        Formula oddEigen = ForAll(
            "v",
            oddChannel,
            Equal(Call("J", v), Neg(v)));

        return Disp(All(
            Equal(Call("J", ePlus), eMinus),
            Equal(Call("J", eMinus), ePlus),
            Equal(even, Mul(half, Add(identity, j))),
            Equal(odd, Mul(half, Sub(identity, j))),
            decomposition,
            Equal(Call("range", even), evenChannel),
            Equal(evenChannel, Call("span", complex, Add(ePlus, eMinus))),
            Equal(Call("range", odd), oddChannel),
            Equal(oddChannel, Call("span", complex, Sub(ePlus, eMinus))),
            Call("IsCompl", evenChannel, oddChannel),
            evenEigen,
            oddEigen));
    }

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)],
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Subscript(string name, Formula subscript) =>
        Seq(F.Id(name), Underscore, Grp(subscript));

    private static Formula Neg(Formula value) => Seq(Minus, value);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate(And);
}
