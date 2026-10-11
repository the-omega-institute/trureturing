using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class FiedlerResistanceInvariantWeightsRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/cruzortegamenendezconde2023fiedlerresistance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Invariant weights cannot maximize the Fiedler value at fixed resistance on K23.",
        H("Fixed resistance does not force an invariant Fiedler maximizer"),
        Blocks(
            Paragraph(Text("Positive edge conductances determine a weighted Laplacian. Algebraic connectivity is its least Rayleigh quotient on nonzero vectors orthogonal to the constants. Effective resistance comes from a harmonic voltage with boundary values one and zero; total resistance sums over unordered pairs of distinct vertices.")),
            Node("lap", "Weighted Laplacian", "wLap", LapFormula(),
                "Section 2, page 3, states: “The laplacian of a weighted graph (G;ω) is the operator on ℓ(V) given by” (L(G,ω)x)i = ∑{vi,vj}∈E ωi,j(xi−xj). The displayed matrix has the weighted degree on the diagonal and negative conductance on each edge. Vertex labels are Fin n; weights are functions on Sym2 (Fin n)."),
            Node("lambda", "Algebraic connectivity", "lambda2", LambdaFormula(),
                "Section 3, page 4, states: “By the Courant-Fischer-Weyl theorem, the algebraic connectivity of a weighted graph is” λ2(G;ω) = min x⊥J ⟨L(G,ω)x,x⟩/⟨x,x⟩. The encoding excludes the zero vector explicitly and uses the infimum of the Rayleigh values."),
            Node("harmonic", "Harmonic boundary data", "Harmonic", HarmonicFormula(),
                "A harmonic voltage has value one at i, zero at j, and zero weighted Laplacian at every other vertex. These are the boundary data used in Section 4 to define current and effective resistance."),
            Node("extension", "Harmonic extension", "harmonicExt", ExtensionFormula(),
                "Section 4, page 5, states: “The vector x̃ is known as the harmonic extension of x.” It requires (Lω x̃)v=0 outside the boundary set. A harmonic vector is chosen when one exists, and the value is zero otherwise. For the positive conductances used on K23, the explicit harmonic certificates exist and are unique for every ordered pair i<j used in totalRes; the zero fallback contributes to none of those resistances."),
            Node("resistance", "Effective resistance", "effRes", ResistanceFormula(),
                "Section 4, Definition 4.1, page 5, states: “Given two vertices vi≠vj of the weighted graph (G;ω), let U={vi,vj}. For h∈ℓ(V) the harmonic extension of the function in ℓ(U) given by hi=1, hj=0, define” r(vi,vj)=⟨Lωh,h⟩⁻¹=(Lωh)i⁻¹. Thus resistance is the reciprocal of the boundary current. The source also defines r(v,v)=0; effRes uses zero on the diagonal."),
            Node("pair", "Unordered-pair resistance", "pairRes", PairFormula(),
                "Sym2.lift orients the representatives of an unordered pair by min and max. Thus each off-diagonal pair uses the same harmonic boundary convention irrespective of the order of its representatives."),
            Node("total", "Total resistance", "totalRes", TotalFormula(),
                "Section 4, page 5, states: “The total effective resistance of (G,ω) is” R(G;ω)=∑{vi,vj} r(vi,vj). The non-diagonal Sym2 pairs count each unordered pair once."),
            Node("feasible", "Fixed-resistance feasible weights", "Feasible", FeasibleFormula(),
                "Feasible weights are strictly positive on edges and have the same total resistance as the unweighted graph. Values on nonedges are unrestricted; edgewise equality suffices to preserve both lambda2 and totalRes."),
            Node("invariant", "Automorphism invariance", "AutInvariant", InvariantFormula(),
                "An automorphism-invariant weight function has the same value on each edge and its image under every graph automorphism. This condition constrains edges only."),
            Node("claim", "The Section 5 conjecture", "claim", ClaimFormula(),
                "Section 5, page 7, states verbatim: “We conjecture that – in the same fashion of what happens with the absolute algebraic connectivity – the maximal value of (3) is attained always for weight distributions that are invariant under automorphisms of the graph.” Equation (3) defines ă(G) = max {λ2(G;ω) | R(G;ω)=R(G)}. The encoding quantifies over connected finite simple graphs of order at least three and asserts an invariant feasible assignment dominating every feasible assignment; it does not assume existence of a maximum separately."),
            Node("result", "Refutation on K23", "result", new Formula.Not(Call("claim")),
                "Let the hubs be 0 and 1 and the leaves be 2, 3 and 4. Conductances 32/23 on the edges incident to hub 0 and 16/23 on those incident to hub 1 give total resistance 23/3, equal to the unweighted value, and algebraic connectivity 48/23. Rayleigh lower bounds and the leaf-difference eigenvector certify that value, while explicit harmonic voltages certify the resistances. Hub and leaf swaps force every invariant feasible assignment to have weight one on each edge and algebraic connectivity two. Since 48/23>2, no invariant assignment can attain the constrained maximum, whether or not the maximum exists.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("cruz-menendez-2023-fiedler-resistance-invariant-weights"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("fk-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula FinN() => Call("Fin", V("n"));
    private static Formula Vector() => Seq(FinN(), Sp, To, Sp, Real());
    private static Formula Weights() => Seq(Call("Sym2", FinN()), Sp, To, Sp, Real());
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Adj(Formula left, Formula right) => QCall("SimpleGraph", "Adj", V("G"), left, right);
    private static Formula Pair(Formula left, Formula right) => Seq(V("s"), Parenthesized(Seq(left, Comma, right)));
    private static Formula Lap() => Call("wLap", V("G"), V("w"));
    private static Formula LapVector(Formula vector) => QCall("Matrix", "mulVec", Lap(), vector);
    private static Formula DotProduct(Formula left, Formula right) => Call("dotProduct", left, right);
    private static Formula SumOver(string name, Formula type, Formula value, Formula? condition = null) =>
        Seq(new Formula.Subscript(Sum, condition is null
            ? Seq(V(name), Sp, Colon, Sp, type)
            : Seq(V(name), Sp, Colon, Sp, type, Sp, Mid, Sp, condition)), Sp, value);
    private static Formula GraphBinders(Formula body, bool decidable = true) =>
        All("n", Nat(), All("G", Call("SimpleGraph", FinN()),
            decidable ? Seq(OpenBracket, Call("DecidableRel", QCall("SimpleGraph", "Adj", V("G"))),
                CloseBracket, Sp, body) : body));
    private static Formula WeightedBinders(Formula body) => GraphBinders(All("w", Weights(), body));
    private static Formula Endpoints(Formula body) => All("i", FinN(), All("j", FinN(), body));

    private static Formula LapFormula()
    {
        Formula diagonal = SumOver("k", FinN(), App(V("w"), Pair(V("i"), V("k"))), Adj(V("i"), V("k")));
        Formula offDiagonal = Call("ite", Adj(V("i"), V("j")),
            new Formula.Negate(App(V("w"), Pair(V("i"), V("j")))), D(0));
        return WeightedBinders(Endpoints(Eqn(App(Lap(), V("i"), V("j")),
            Call("ite", Eqn(V("i"), V("j")), diagonal, offDiagonal))));
    }

    private static Formula LambdaFormula()
    {
        Formula quotient = new Formula.Fraction(DotProduct(V("x"), LapVector(V("x"))), DotProduct(V("x"), V("x")));
        Formula values = Seq(OpenBrace, V("r"), Sp, Colon, Sp, Real(), Sp, Mid, Sp,
            Exists("x", Vector(), And(Ne(V("x"), D(0)), And(Eqn(SumOver("i", FinN(), App(V("x"), V("i"))), D(0)),
                Eqn(V("r"), quotient)))), CloseBrace);
        return WeightedBinders(Eqn(Call("lambda2", V("G"), V("w")), Call("sInf", values)));
    }

    private static Formula HarmonicFormula() => WeightedBinders(Endpoints(All("x", Vector(),
        Eqn(Call("Harmonic", V("G"), V("w"), V("i"), V("j"), V("x")),
            And(Eqn(App(V("x"), V("i")), D(1)), And(Eqn(App(V("x"), V("j")), D(0)),
                All("k", FinN(), Imp(Ne(V("k"), V("i")), Imp(Ne(V("k"), V("j")),
                    Eqn(App(LapVector(V("x")), V("k")), D(0)))))))))));

    private static Formula ExtensionFormula()
    {
        Formula exists = Exists("x", Vector(), Call("Harmonic", V("G"), V("w"), V("i"), V("j"), V("x")));
        Formula choice = Seq(Call("if"), Sp, V("h"), Sp, Colon, Sp, Parenthesized(exists), Sp,
            Call("then"), Sp, QCall("Classical", "choose", V("h")), Sp, Call("else"), Sp, D(0));
        return WeightedBinders(Endpoints(Eqn(Call("harmonicExt", V("G"), V("w"), V("i"), V("j")), choice)));
    }

    private static Formula ResistanceFormula()
    {
        Formula extension = Call("harmonicExt", V("G"), V("w"), V("i"), V("j"));
        return WeightedBinders(Endpoints(Eqn(Call("effRes", V("G"), V("w"), V("i"), V("j")),
            Call("ite", Eqn(V("i"), V("j")), D(0), new Formula.Fraction(D(1), App(LapVector(extension), V("i")))))));
    }

    private static Formula PairFormula() => WeightedBinders(Endpoints(
        Eqn(Call("pairRes", V("G"), V("w"), Pair(V("i"), V("j"))),
            Call("effRes", V("G"), V("w"), Call("min", V("i"), V("j")), Call("max", V("i"), V("j"))))));

    private static Formula TotalFormula() => WeightedBinders(
        Eqn(Call("totalRes", V("G"), V("w")), SumOver("p", Call("Sym2", FinN()),
            Call("pairRes", V("G"), V("w"), V("p")), new Formula.Not(QCall("Sym2", "IsDiag", V("p"))))));

    private static Formula FeasibleFormula() => WeightedBinders(
        Eqn(Call("Feasible", V("G"), V("w")),
            And(All("e", Call("Sym2", FinN()), Imp(Member(V("e"), QCall("SimpleGraph", "edgeSet", V("G"))),
                Lt(D(0), App(V("w"), V("e"))))),
                Eqn(Call("totalRes", V("G"), V("w")), Call("totalRes", V("G"), D(1))))));

    private static Formula InvariantFormula() => GraphBinders(All("w", Weights(),
        Eqn(Call("AutInvariant", V("G"), V("w")),
            All("sigma", QCall("SimpleGraph", "Iso", V("G"), V("G")),
                All("e", Call("Sym2", FinN()), Imp(Member(V("e"), QCall("SimpleGraph", "edgeSet", V("G"))),
                    Eqn(App(V("w"), QCall("Sym2", "map", V("sigma"), V("e"))), App(V("w"), V("e")))))))), false);

    private static Formula ClaimFormula()
    {
        Formula maximal = All("v", Weights(), Imp(Call("Feasible", V("G"), V("v")),
            Leq(Call("lambda2", V("G"), V("v")), Call("lambda2", V("G"), V("w")))));
        Formula assignment = Exists("w", Weights(), And(Call("Feasible", V("G"), V("w")),
            And(Call("AutInvariant", V("G"), V("w")), maximal)));
        return Eqn(Call("claim"), GraphBinders(Imp(QCall("SimpleGraph", "Connected", V("G")),
            Imp(Leq(D(3), V("n")), assignment))));
    }
}
