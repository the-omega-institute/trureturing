using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class ExponentialSectorKernelEquilibriumWeightsDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Quantum/Entanglement/ExponentialSectorKernelEquilibriumWeights.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive exponential weights have explicit endpoint and interior coordinates for every real site sequence.",
        H("Coordinates of Recursive Exponential Weights"),
        Blocks(
            Paragraph(Text(
                "For any real sequence loss, edge(loss,i) is exp(-(loss(i+1)-loss(i))/2). "
                + "The existing equilibriumWeight recursion starts with singleton weight one. "
                + "At stage m+1 it retains each earlier coordinate except the former last, "
                + "from which it subtracts edge(loss,m)/(1+edge(loss,m)); the new last "
                + "coordinate is 1/(1+edge(loss,m)). No ordering assumption is needed "
                + "to define this recursion.")),
            Describe.Lean(
                DescribeId.Create("endpoint-interior-coordinates"),
                DeclarationHandle.Create(Module + "equilibrium_weight_endpoint_interior"),
                H("All coordinates at every size"),
                StatementSource.FromAuthor(Coordinates()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The stage n+1 has n+2 coordinates, indexed by Fin(n+2). "
                        + "Its first index is zero and its last is Fin.last(n+1). "
                        + "For i in Fin(n), succ(castSucc(i)) is the interior index i+1; "
                        + "the adjacent coefficients are edge(loss,i) and edge(loss,i+1). "
                        + "In edge(loss,i), the Fin index is coerced to its natural value.")),
                    Paragraph(Text(
                        "Induction preserves the initial coordinate whenever a later site is appended. "
                        + "An old interior coordinate is also preserved. The former endpoint becomes "
                        + "a new interior coordinate, and subtracting the new correction gives "
                        + "the displayed sum of the two adjacent reciprocals minus one. "
                        + "Exponentials are positive, so every denominator 1+edge(loss,i) is nonzero.")),
                    Paragraph(Text(
                        "For n=0 this is the two-site stage: both endpoint weights are "
                        + "1/(1+edge(loss,0)), and the interior quantifier over Fin(0) is empty. "
                        + "The singleton stage has weight one and lies outside this reindexing.")),
                    Paragraph(Text(
                        "For strictly increasing ordered sites, the ordered-kernel row equations "
                        + "and positivity identify these recursive weights with the positive "
                        + "equilibrium vector. With the inverse kernel on those distinct sites, "
                        + "Kv=1 gives v=K inverse times the ones vector. Normalization by its "
                        + "positive total mass gives the ordered simplex point. For arbitrary "
                        + "loss the coordinate statement gives no weight positivity or "
                        + "probability interpretation; physical channel optimality requires "
                        + "its separate channel identification."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Reciprocal(Formula loss, Formula i) =>
        Seq(Frac, Grp(D(1)), Grp(Add(D(1), Call("edge", loss, i))));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Coordinates()
    {
        Formula n = F.Id("n");
        Formula loss = F.Id("loss");
        Formula i = F.Id("i");
        Formula size = Add(n, D(1));
        Formula first = Equal(Call("equilibriumWeight", size, loss, D(0)), Reciprocal(loss, D(0)));
        Formula last = Equal(Call("equilibriumWeight", size, loss, Call("last", size)), Reciprocal(loss, n));
        Formula interior = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("i"), Call("Fin", n),
            Equal(Call("equilibriumWeight", size, loss, Call("succ", Call("castSucc", i))),
                Seq(Reciprocal(loss, i), Sp, Plus, Sp, Reciprocal(loss, Add(i, D(1))), Sp, Minus, Sp, D(1))));
        Formula body = new Formula.Logic(first, FormulaLogicOperator.And,
            new Formula.Logic(last, FormulaLogicOperator.And, interior));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), naturals,
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("loss"),
                Seq(naturals, Sp, To, Sp, reals), body)));
    }
}
