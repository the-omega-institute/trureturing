using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroForcing;

internal sealed class GridPowerZeroForcingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/abiadflaggghaseminezhadzeijlemaker2026powers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjecture 12 as printed fails: two initially black vertices force the three-by-two grid at power one, whereas the conjectured value is three.",
        H("The unrestricted grid-power zero-forcing conjecture is false"),
        Blocks(
            Describe.Lean(DescribeId.Create("gridpower-power"), DeclarationHandle.Create(Prefix + "graphPower"),
                H("Distance powers"), StatementSource.FromAuthor(PowerFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Section 2 defines the graph power on the same vertices by 1 ≤ distance ≤ k. The compiled definition uses distinct endpoints and SimpleGraph.edist, the shortest-walk length in extended natural numbers. Distinct endpoints have positive extended distance; unreachable endpoints have infinite distance and cannot be adjacent for a natural k. This gives the source semantics throughout the quantified domain, including all powers, rather than defining only the counterexample. The grid is Mathlib's Cartesian product of its n-vertex pathGraph."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gridpower-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 12 as printed"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Exact source quote: Let b≥1, k≥1 and ℓ≥k+1. Then Z((P_b □ P_ℓ)^k)=bk. All three parameters are natural numbers; no b≤ℓ assumption is present. Fin n labels the source's n vertices by 0 through n−1. The imported zeroForcingNumber is the minimum cardinality of an initial finite black set whose Black closure is all vertices. Black.force is the ordinary unique-white-neighbor rule; no positive semidefinite or multiple-neighbor forcing variant is used. The full source immediately cites the classical k=1 formula min(b,ℓ) and reports computational support on a range containing (3,2,1); the classical formula conflicts with the unrestricted conjecture, and the reported computational support conflicts with the explicit counterexample. The classical formula is existing mathematics, not a novelty claim."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gridpower-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The three-by-two counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Use b=3, k=1, ℓ=2. Label the vertices A=(0,0), B=(0,1), C=(1,0), D=(1,1), E=(2,0), F=(2,1). The edges are AB, AC, BD, CD, CE, DF and EF. With A and B initially black, the forces A→C, B→D, C→E, D→F color all six vertices. At each force, every neighbor other than the target is already black. Mathlib's edist_le_one_iff_adj_or_eq identifies the first graph power with the base graph. Nat.sInf_le applied to the two-element forcing set gives zeroForcingNumber≤2, contradicting the proposed value 3. Exact Z is unnecessary. The proof instantiates existing forcing constructors and distance/minimum interfaces and checks finite facts. A corrected conjecture with b≤ℓ is outside this result."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("abiad-flagg-ghasemi-nezhad-zeijlemaker-2026-grid-power-zero-forcing"),
                    ResolutionKind.Refuted))), []));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Par(a), op, Par(b));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula PowerFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), k = F.Id("k"), x = F.Id("x"), y = F.Id("y");
        Formula adj = Seq(Call("graphPower", g, k), Dot, Call("Adj", x, y));
        Formula bound = Le(Call("edist", g, x, y), Par(Seq(k, Colon, F.Id("ENat"))));
        Formula body = Logic(Rel(x, FormulaRelationOperator.NotEqual, y), FormulaLogicOperator.And, bound);
        return Disp(All("V", F.Id("Type"), All("G", Call("SimpleGraph", v), All("k", N,
            All("x", v, All("y", v, Logic(adj, FormulaLogicOperator.Iff, body)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula b = F.Id("b"), k = F.Id("k"), ell = F.Id("ell");
        Formula grid = Call("boxProd", Call("pathGraph", b), Call("pathGraph", ell));
        Formula z = Call("zeroForcingNumber", Call("graphPower", grid, k));
        Formula rhs = new Formula.Binary(b, FormulaBinaryOperator.Multiply, k);
        Formula kp = new Formula.Binary(k, FormulaBinaryOperator.Add, D(1));
        Formula body = Logic(Le(D(1), b), FormulaLogicOperator.Implies,
            Logic(Le(D(1), k), FormulaLogicOperator.Implies,
                Logic(Le(kp, ell), FormulaLogicOperator.Implies, Eq(z, rhs))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All("b", N, All("k", N, All("ell", N, body)))));
    }
}
