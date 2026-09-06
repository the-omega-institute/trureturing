using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class OddPrimePerfectOneFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.";

    private static readonly LibraryNoteRef Kotzig = LibraryNoteRef.Create(
        "D5/L/Arith/kotzig1964perfectonefactorization");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kotzig's construction gives a perfect one-factorization of the complete graph "
            + "on one point adjoining the residues modulo an odd prime.",
        H("Odd-Prime Perfect One-Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kotzig-vertex-type"),
                DeclarationHandle.Create(Prefix + "Vertex"),
                H("Kotzig vertex type"),
                StatementSource.FromAuthor(VertexFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This repository formulation uses the classical Kotzig family as context. "
                        + "For a natural modulus p, the vertex type is exactly Option (ZMod p); "
                        + "the none vertex denotes the distinguished point at infinity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kotzig-partner-map"),
                DeclarationHandle.Create(Prefix + "partner"),
                H("Partner map in one factor"),
                StatementSource.FromAuthor(PartnerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This repository definition formulates the partner map in the classical "
                        + "Kotzig family. The factor indexed by a pairs infinity with a. Every other finite vertex "
                        + "x is paired with 2a-x, while the finite vertex a is paired back with "
                        + "infinity. The displayed ite is the exact branch structure of the Lean "
                        + "definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kotzig-factor-graph"),
                DeclarationHandle.Create(Prefix + "factor"),
                H("Factor graph from the partner relation"),
                StatementSource.FromAuthor(FactorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This repository definition formulates the classical Kotzig factor graph "
                        + "as exactly SimpleGraph.fromRel applied to the relation "
                        + "v = partner(a,u). The orientation shown here matches the Lean defining "
                        + "expression; fromRel supplies symmetry and removes loops."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("union-of-two-kotzig-factors"),
                DeclarationHandle.Create(Prefix + "pairGraph"),
                H("Union of two factors"),
                StatementSource.FromAuthor(PairGraphFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This repository definition uses the classical Kotzig family as context. "
                        + "The pair graph is the lattice supremum, equivalently the edge union, of "
                        + "the factors indexed by a and b."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("alternating-reflection-translation-step"),
                DeclarationHandle.Create(Prefix + "translationStep"),
                H("Alternating-reflection translation step"),
                StatementSource.FromAuthor(TranslationStepFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This repository definition records the translation used in its proof of "
                        + "the classical Kotzig family. Composing the two affine reflections gives displacement 2(b-a); "
                        + "in the partner graph that displacement is reached in one or two edges "
                        + "(the exceptional vertices are handled by a single edge)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("edge-owner-infinity"),
                DeclarationHandle.Create(Prefix + "edge_owner_infinity"),
                H("Owner of an edge incident to infinity"),
                StatementSource.FromAuthor(EdgeOwnerInfinityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The edge from none to some x is in factor a exactly when a equals x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edge-owner-pair"),
                DeclarationHandle.Create(Prefix + "edge_owner_pair"),
                H("Owner of a finite edge"),
                StatementSource.FromAuthor(EdgeOwnerPairFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For distinct finite vertices x and y, the owner is their midpoint. "
                        + "The displayed fraction is field division in ZMod p, with denominator "
                        + "two coerced into that field; it is not natural-number division."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinct-factor-pair-is-two-regular"),
                DeclarationHandle.Create(Prefix + "pairGraph_two_regular"),
                H("Distinct factors have two neighbors at every vertex"),
                StatementSource.FromAuthor(TwoRegularFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This helper proof is repository work in the context of the classical "
                        + "Kotzig family. When a and b are distinct, the two partner vertices are distinct, so every "
                        + "neighbor set in pairGraph(a,b) has set cardinality two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translation-step-has-full-additive-order"),
                DeclarationHandle.Create(Prefix + "translationStep_addOrderOf"),
                H("The translation step has full additive order"),
                StatementSource.FromAuthor(TranslationOrderFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This helper proof is repository work in the context of the classical "
                        + "Kotzig family. For distinct a and b and odd prime p, 2(b-a) is nonzero in ZMod p. Its "
                        + "additive order is therefore the prime p."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kotzig-odd-prime-perfect-one-factorization"),
                DeclarationHandle.Create(Prefix + "odd_prime_perfect_one_factorization"),
                H("Kotzig's odd-prime perfect one-factorization"),
                StatementSource.FromAuthor(PerfectOneFactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed reflection-factor family is the Kotzig GK construction, "
                            + "named in the scoped Library note only for p >= 11. Its three "
                            + "properties for every odd prime, including p = 3, 5, 7, are proved "
                            + "here. The note attests existence, not this explicit formulation.")),
                    Paragraph(Text(
                        "For every odd prime p, every factor is a perfect matching on Option "
                            + "(ZMod p), and every pair of distinct vertices belongs to exactly "
                            + "one indexed factor.")),
                    Paragraph(Text(
                        "For distinct indices a and b, alternating the two partner reflections "
                            + "reaches x+2(b-a) from x in one or two edges. Since this nonzero "
                            + "translation generates additive ZMod p, the two-regular pair graph "
                            + "is connected; Mathlib's connected-cycle theorem then supplies a "
                            + "Hamiltonian cycle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("existence-of-odd-prime-perfect-one-factorization"),
                DeclarationHandle.Create(Prefix + "exists_odd_prime_perfect_one_factorization"),
                H("Existence of an odd-prime perfect one-factorization"),
                StatementSource.FromAuthor(ExistenceFormula()),
                AssessedProvenance.FromLiterature(Kotzig),
                Blocks(Paragraph(Text(
                    "For every odd prime p, K_{p+1} admits a perfect one-factorization. "
                        + "The Library note attests this existence statement: Section 5 names "
                        + "Kotzig's GK family for p >= 11, and Section 1 records existence at "
                        + "p = 3, 5, 7. Here the existential factors range over arbitrary "
                        + "graphs on Option (ZMod p); the proof instantiates them with the "
                        + "reflection factors of the preceding theorem."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Joined(arguments, Comma)));

    private static Formula QualifiedCall(
        string qualifier,
        string name,
        params Formula[] arguments) =>
        Seq(
            Operatorname, Grp(F.Id(qualifier)), Dot,
            Operatorname, Grp(F.Id(name)),
            Parenthesized(Joined(arguments, Comma)));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ZMod(Formula p) => Call("ZMod", p);
    private static Formula VertexOf(Formula p) => Call("Vertex", p);
    private static Formula Factor(Formula a) => Call("factor", a);
    private static Formula PairGraph(Formula a, Formula b) => Call("pairGraph", a, b);
    private static Formula Partner(Formula a, Formula v) => Call("partner", a, v);
    private static Formula Some(Formula value) => Call("some", value);
    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Sp, InMacro, Sp, type);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);
    private static Formula ImpliesFormula(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Rightarrow, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(params Formula[] clauses) => Joined(clauses, Land);
    private static Formula ParenthesizedConjunction(params Formula[] clauses) =>
        Joined([.. clauses.Select(Parenthesized)], Land);
    private static Formula CoercedTwo(Formula p) =>
        Parenthesized(Seq(D(2), Colon, Sp, ZMod(p)));

    private static Formula PrimePrefix(Formula p) => Seq(
        Forall, Sp, Typed(p, Naturals()), Comma, RowBreak, Grp(),
        OpenBracket, Call("Fact", Call("Prime", p)), CloseBracket, Comma, RowBreak, Grp());

    private static Formula VertexFormula()
    {
        Formula p = F.Id("p");
        return Disp(Seq(
            Forall, Sp, Typed(p, Naturals()), Comma, RowBreak, Grp(),
            VertexOf(p), Sp, Colon, Eq, Sp, Call("Option", ZMod(p)), Dot));
    }

    private static Formula PartnerFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), x = F.Id("x");
        Formula finiteBranch = Call(
            "ite",
            Equal(x, a),
            F.Id("none"),
            Some(Seq(CoercedTwo(p), Sp, Cdot, Sp, a, Sp, Minus, Sp, x)));
        return Disp(Seq(
            Forall, Sp, Typed(p, Naturals()), Comma, Sp,
            Typed(a, ZMod(p)), Comma, Sp, Typed(x, ZMod(p)), Comma, RowBreak, Grp(),
            ParenthesizedConjunction(
                Equal(Partner(a, F.Id("none")), Some(a)),
                Equal(Partner(a, Some(x)), finiteBranch)), Dot));
    }

    private static Formula FactorFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), u = F.Id("u"), v = F.Id("v");
        Formula relation = Parenthesized(Seq(
            u, Comma, Sp, v, Colon, Sp, VertexOf(p), Sp, Mapsto, Sp,
            Equal(v, Partner(a, u))));
        return Disp(Seq(
            Forall, Sp, Typed(p, Naturals()), Comma, Sp, Typed(a, ZMod(p)), Comma,
            RowBreak, Grp(),
            Factor(a), Sp, Colon, Eq, Sp,
            QualifiedCall("SimpleGraph", "fromRel", relation), Dot));
    }

    private static Formula PairGraphFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), b = F.Id("b");
        return Disp(Seq(
            Forall, Sp, Typed(p, Naturals()), Comma, Sp,
            Typed(a, ZMod(p)), Comma, Sp, Typed(b, ZMod(p)), Comma, RowBreak, Grp(),
            PairGraph(a, b), Sp, Colon, Eq, Sp,
            Call("sup", Factor(a), Factor(b)), Dot));
    }

    private static Formula TranslationStepFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), b = F.Id("b");
        return Disp(Seq(
            Forall, Sp, Typed(p, Naturals()), Comma, Sp,
            Typed(a, ZMod(p)), Comma, Sp, Typed(b, ZMod(p)), Comma, RowBreak, Grp(),
            Call("translationStep", a, b), Sp, Colon, Eq, Sp,
            CoercedTwo(p), Sp, Cdot, Sp, Parenthesized(Seq(b, Sp, Minus, Sp, a)), Dot));
    }

    private static Formula TwoRegularFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), b = F.Id("b"), v = F.Id("v");
        Formula hypotheses = Conjunction(NotEqual(p, D(2)), NotEqual(a, b));
        Formula conclusion = Seq(
            Forall, Sp, Typed(v, VertexOf(p)), Comma, RowBreak, Grp(),
            Equal(Call("ncard", Call("neighborSet", PairGraph(a, b), v)), D(2)));
        return Disp(Seq(
            PrimePrefix(p),
            Forall, Sp, Typed(a, ZMod(p)), Comma, Sp, Typed(b, ZMod(p)), Comma,
            RowBreak, Grp(), ImpliesFormula(hypotheses, conclusion), Dot));
    }

    private static Formula EdgeOwnerInfinityFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), x = F.Id("x");
        Formula conclusion = Seq(
            Call("Adj", Factor(a), F.Id("none"), Some(x)), Sp, Iff, Sp, Equal(a, x));
        return Disp(Seq(
            PrimePrefix(p),
            Forall, Sp, Typed(a, ZMod(p)), Comma, Sp, Typed(x, ZMod(p)), Comma,
            RowBreak, Grp(), ImpliesFormula(NotEqual(p, D(2)), conclusion), Dot));
    }

    private static Formula EdgeOwnerPairFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), x = F.Id("x"), y = F.Id("y");
        Formula midpoint = new Formula.Fraction(
            Parenthesized(Seq(x, Sp, Plus, Sp, y)), CoercedTwo(p));
        Formula hypotheses = Conjunction(NotEqual(p, D(2)), NotEqual(x, y));
        Formula conclusion = Seq(
            Call("Adj", Factor(a), Some(x), Some(y)), Sp, Iff, Sp, Equal(a, midpoint));
        return Disp(Seq(
            PrimePrefix(p),
            Forall, Sp, Typed(a, ZMod(p)), Comma, Sp,
            Typed(x, ZMod(p)), Comma, Sp, Typed(y, ZMod(p)), Comma,
            RowBreak, Grp(), ImpliesFormula(hypotheses, conclusion), Dot));
    }

    private static Formula TranslationOrderFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), b = F.Id("b");
        Formula hypotheses = Conjunction(NotEqual(p, D(2)), NotEqual(a, b));
        Formula conclusion = Equal(
            Call("addOrderOf", Call("translationStep", a, b)), p);
        return Disp(Seq(
            PrimePrefix(p),
            Forall, Sp, Typed(a, ZMod(p)), Comma, Sp, Typed(b, ZMod(p)), Comma,
            RowBreak, Grp(), ImpliesFormula(hypotheses, conclusion), Dot));
    }

    private static Formula PerfectOneFactorizationFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), b = F.Id("b");
        Formula u = F.Id("u"), v = F.Id("v");
        Formula perfectMatching = Seq(
            Forall, Sp, Typed(a, ZMod(p)), Comma, Sp,
            Call("IsPerfectMatching", Parenthesized(Seq(
                Operatorname, Grp(F.Id("Top")), Dot, Operatorname, Grp(F.Id("top")),
                Colon, Sp, QualifiedCall("SimpleGraph", "Subgraph", Factor(a))))));
        Formula uniqueOwner = Seq(
            Forall, Sp, Typed(u, VertexOf(p)), Comma, Sp, Typed(v, VertexOf(p)), Comma,
            RowBreak, Grp(), ImpliesFormula(
                NotEqual(u, v),
                Seq(Exists, Bang, Sp, Typed(a, ZMod(p)), Comma, Sp,
                    Call("Adj", Factor(a), u, v))));
        Formula hamiltonian = Seq(
            Forall, Sp, Typed(a, ZMod(p)), Comma, Sp, Typed(b, ZMod(p)), Comma,
            RowBreak, Grp(), ImpliesFormula(
                NotEqual(a, b), Call("IsHamiltonian", PairGraph(a, b))));
        Formula conclusion = ParenthesizedConjunction(
            perfectMatching, uniqueOwner, hamiltonian);
        return Disp(Seq(
            PrimePrefix(p),
            ImpliesFormula(NotEqual(p, D(2)), conclusion), Dot));
    }

    private static Formula ExistenceFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), b = F.Id("b");
        Formula u = F.Id("u"), v = F.Id("v");
        Formula factors = Seq(Operatorname, Grp(F.Id("factors")));
        Formula factorA = Call("factors", a), factorB = Call("factors", b);
        Formula perfectMatching = Seq(
            Forall, Sp, Typed(a, ZMod(p)), Comma, Sp,
            Call("IsPerfectMatching", Parenthesized(Seq(
                Operatorname, Grp(F.Id("Top")), Dot, Operatorname, Grp(F.Id("top")),
                Colon, Sp, QualifiedCall("SimpleGraph", "Subgraph", factorA)))));
        Formula uniqueOwner = Seq(
            Forall, Sp, Typed(u, VertexOf(p)), Comma, Sp, Typed(v, VertexOf(p)), Comma,
            RowBreak, Grp(), ImpliesFormula(
                NotEqual(u, v),
                Seq(Exists, Bang, Sp, Typed(a, ZMod(p)), Comma, Sp,
                    Call("Adj", factorA, u, v))));
        Formula hamiltonian = Seq(
            Forall, Sp, Typed(a, ZMod(p)), Comma, Sp, Typed(b, ZMod(p)), Comma,
            RowBreak, Grp(), ImpliesFormula(
                NotEqual(a, b), Call("IsHamiltonian", Call("sup", factorA, factorB))));
        Formula conclusion = Seq(
            Exists, Sp, factors, Colon, Sp,
            Parenthesized(Seq(ZMod(p), Sp, To, Sp, Call("SimpleGraph", VertexOf(p)))),
            Comma, RowBreak, Grp(),
            ParenthesizedConjunction(perfectMatching, uniqueOwner, hamiltonian));
        return Disp(Seq(
            PrimePrefix(p),
            ImpliesFormula(NotEqual(p, D(2)), conclusion), Dot));
    }

    private static Formula Joined(Formula[] values, Formula separator)
    {
        List<Formula> items = [];
        for (int index = 0; index < values.Length; index++)
        {
            if (index > 0) { items.Add(Sp); items.Add(separator); items.Add(Sp); }
            items.Add(values[index]);
        }
        return Seq([.. items]);
    }
}
