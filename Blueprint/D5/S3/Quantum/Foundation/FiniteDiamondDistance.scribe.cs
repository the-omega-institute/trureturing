using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FiniteDiamondDistanceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/FiniteDiamondDistance.";

    public DocumentDefinition Create()
    {
        Formula r = F.Id("r"), a = F.Id("a"), b = F.Id("b");
        Formula c = F.Id("c"), d = F.Id("d"), x = F.Id("X");
        Formula rho = F.Id("rho"), tau = F.Id("tau"), v = F.Id("v");
        Formula i = F.Id("i"), j = F.Id("j"), u = F.Id("u"), w = F.Id("w");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula pair = Call("Product", r, a);
        Formula state = Call("DensityState", pair);
        Formula channel = Call("QuantumChannel", a, b);
        Formula matrix = Call("Matrix", pair, pair, complex);
        Formula fixedPair = Call("Product", Call("Fin", Call("card", a)), a);
        Formula Error(Formula input) => Call("referenceError", c, d, input);
        Formula Raw(Formula input) => Call("raw", input);
        Formula RankOne(Formula vector) => Call("vecMulVec", vector, Call("star", vector));
        Formula Types(Formula body) => All(
            [Bound("r", F.Id("FiniteType")), Bound("a", F.Id("FiniteType")),
                Bound("b", F.Id("FiniteType")), Bound("c", channel)], body);
        Formula Inputs(Formula body) => Types(All(
            [Bound("d", channel), Bound("rho", state)], body));
        Formula Reduction(Formula outputState) => All(
            [Bound("r", F.Id("FiniteType")), Bound("rho", state)],
            Exists([Bound("tau", outputState)],
                And(Call("IsPure", tau), Le(Error(rho), Error(tau)))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite reference amplification and unhalved stabilized distance for canonical quantum channels.",
            H("Finite Reference Channel Distance"),
            Blocks(
                Paragraph(Text(
                    "All coordinate types are finite and have decidable equality. The reference "
                    + "coordinate is the first factor of each product. QuantumChannel and "
                    + "DensityState are the canonical completely positive, trace-preserving "
                    + "channel and positive trace-one state types. raw converts a state value "
                    + "or a CStarMatrix to its ordinary matrix coordinates. block(X,i,j) is the "
                    + "input matrix with entries X((i,u),(j,w)); channelMatrixAction applies "
                    + "the channel to that matrix. entry evaluates a matrix at two coordinates.")),
                Item("referenceLinear", "Reference-amplified linear map", Types(All(
                    [Bound("X", matrix), Bound("i", r), Bound("j", r),
                        Bound("u", b), Bound("w", b)],
                    Eqn(Call("entry", Call("referenceLinear", c, x),
                            Call("pair", i, u), Call("pair", j, w)),
                        Call("entry", Call("channelMatrixAction", c,
                            Call("block", x, i, j)), u, w)))), true),
                Item("referenceAction", "Reference-amplified action", Types(All(
                    [Bound("X", matrix)], Eqn(Call("referenceAction", c, x),
                        Call("referenceLinear", c, x)))), true),
                Item("referenceState", "Amplified density state", Types(All(
                    [Bound("rho", state)], Eqn(Raw(Call("referenceState", c, rho)),
                        Raw(Call("referenceAction", c, Call("value", rho)))))), true),
                Item("referenceError", "Unhalved error at a joint input", Inputs(Eqn(Error(rho),
                    Call("traceNorm", Sub(Raw(Call("referenceState", c, rho)),
                        Raw(Call("referenceState", d, rho)))))), true),
                Item("IsPure", "Pure density state", All(
                    [Bound("q", F.Id("FiniteType")),
                        Bound("rho", Call("DensityState", F.Id("q")))],
                    Iff(Call("IsPure", rho), Exists(
                        [Bound("v", Call("Function", F.Id("q"), complex))],
                        Eqn(Raw(rho), RankOne(v))))), true),
                Item("pureState", "State of a unit vector", All(
                    [Bound("q", F.Id("FiniteType")),
                        Bound("v", Call("Function", F.Id("q"), complex))],
                    Implies(Eqn(Call("dotProduct", Call("star", v), v), Num(1)),
                        Eqn(Raw(Call("pureState", v)), RankOne(v)))), true),
                Paragraph(Text(
                    "finiteReferenceErrors(c,d) consists of zero and every referenceError(c,d,rho) "
                    + "with a natural number n and rho a DensityState on Fin(n) times a. The "
                    + "unhalved stabilized distance is the real supremum of this set. The zero "
                    + "element includes empty input types, which have no density state.")),
                Item("diamondDistance", "Unhalved stabilized distance", All(
                    [Bound("a", F.Id("FiniteType")), Bound("b", F.Id("FiniteType")),
                        Bound("c", channel), Bound("d", channel)],
                    Eqn(Call("diamondDistance", c, d),
                        Call("sSup", Call("finiteReferenceErrors", c, d)))), true),
                Paragraph(Text(
                    "pureFixedReferenceErrors(c,d) consists of zero and every referenceError(c,d,tau) "
                    + "for a pure DensityState tau on Fin(card(a)) times a. Reference and input "
                    + "types may inhabit independent universes. Each joint density state is "
                    + "dominated in error by a pure state on the same reference, and by a pure "
                    + "state with reference dimension card(a). No nonempty-type assumption is needed.")),
                Item("result", "Pure inputs and a fixed reference dimension", All(
                    [Bound("a", F.Id("FiniteType")), Bound("b", F.Id("FiniteType")),
                        Bound("c", channel), Bound("d", channel)],
                    And(Reduction(state), And(Reduction(Call("DensityState", fixedPair)),
                        Eqn(Call("diamondDistance", c, d),
                            Call("sSup", Call("pureFixedReferenceErrors", c, d))))))))));
    }

    private static DocumentBlock Item(string name, string title, Formula formula, bool definition = false) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(Explanation(name)))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static string Explanation(string name) => name switch
    {
        "referenceLinear" => "Each reference block is transformed by the same channel linear map.",
        "referenceAction" => "This evaluates the reference-amplified linear map on a joint matrix.",
        "referenceState" => "Complete positivity preserves the joint matrix order, and trace preservation preserves the sum of the diagonal reference-block traces.",
        "referenceError" => "The state difference is measured by its trace norm without the conventional division by two.",
        "IsPure" => "A pure state is represented by one vector outer product.",
        "pureState" => "The vector outer product is positive, and its trace is the squared vector norm.",
        "diamondDistance" => "Every natural-number reference dimension participates in the supremum.",
        "result" => "A spectral decomposition reduces mixed inputs to pure inputs. Factorization of the pure-state coefficient matrix compresses the reference to at most the input dimension. Reference isometries preserve the channel error, so the stabilized supremum equals the pure-state supremum at that fixed dimension.",
        _ => throw new System.ArgumentOutOfRangeException(nameof(name))
    };

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Exists(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
