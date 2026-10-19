using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class TarnauceanuReciprocalSubgroupOrdersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/tarnauceanu2024reciprocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The subgroup-order reciprocal sum has no universal lower bound above one on finite non-cyclic groups.",
        H("Tărnăuceanu's reciprocal subgroup-order conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tarnauceanu-reciprocal-sum"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.f"),
                H("The reciprocal subgroup-order sum"),
                StatementSource.FromAuthor(FFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The source states on printed p. 116: “In the current note, we consider "
                    + "the function f(G) = Σ_{H∈L(G)} 1/|H|.” Here L(G) is the subgroup "
                    + "lattice, including the trivial subgroup and the whole group. The displayed "
                    + "definition sums the reciprocal real cardinality of every subgroup."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tarnauceanu-conjecture-claim"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.claim"),
                H("Conjecture 3.1"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The source states on printed p. 119: “There is no constant c > 1 such "
                    + "that f(G) > c, for all finite non-cyclic groups G.” The Lean statement "
                    + "quantifies over every carrier type with its group and finite instances and "
                    + "expresses the strict inequality using the reciprocal subgroup-order sum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tarnauceanu-conjecture-result"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.result"),
                H("Conjecture 3.1 holds"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For any c > 1, choose a large prime q, then a prime p congruent to one "
                        + "modulo q, and finally an exponent s. The frozen split extension of "
                        + "Cyclic p by Cyclic (q^s) is non-cyclic. Its subgroups are inverse images "
                        + "of quotient subgroups, proper embedded quotient subgroups, and conjugates "
                        + "of the full complement. The resulting reciprocal sum is bounded by "
                        + "(1/p)·q/(q−1) + q/(q−1) + p/q^s. Letting q and then s grow makes "
                        + "the excess over one smaller than c−1.")),
                    Paragraph(Text(
                        "The argument uses the elementary prime supplier for primes congruent to one "
                        + "modulo q and therefore does not assume infinitely many Sophie Germain primes. "
                        + "The proof concerns finite non-cyclic groups and gives no rate statement for "
                        + "the least value at a fixed group order."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tarnauceanu-2024-reciprocal-subgroup-orders"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(F.Id(name), [.. xs]);

    private static Formula NatCall(string member, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(Seq(F.Id("Nat"), Dot, F.Id(member)))), [.. xs]);

    private static Formula Typed(Formula variable, Formula type) =>
        Seq(variable, Sp, Colon, Sp, type);

    private static Formula Lambda(Formula variable, Formula type, Formula body) =>
        Seq(Operatorname, Grp(F.Id("fun")), Sp, Typed(variable, type), Sp, Mapsto, Sp, body);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Instances(Formula g, Formula body) =>
        Seq(OpenBracket, Call("Group", g), CloseBracket, Sp,
            Seq(OpenBracket, Call("Finite", g), CloseBracket, Sp, body));

    private static Formula GroupInstance(Formula g, Formula body) =>
        Seq(OpenBracket, Call("Group", g), CloseBracket, Sp, body);

    private static Formula FFormula()
    {
        var g = F.Id("G");
        var h = F.Id("H");
        var card = NatCall("cast", NatCall("card", h));
        var summand = new Formula.Fraction(D(1), card);
        var sum = Call("finsum", Lambda(h, Call("Subgroup", g), summand));
        return Disp(All("G", F.Id("Type"), GroupInstance(g,
            Seq(Call("f", g), Sp, Eq, Sp, sum))));
    }

    private static Formula ClaimBody()
    {
        var c = F.Id("c");
        var g = F.Id("G");
        var groupBody = Instances(g,
            Imp(new Formula.Not(Call("IsCyclic", g)), Lt(c, Call("f", g))));
        var universal = All("G", F.Id("Type"), groupBody);
        var exists = Ex("c", Seq(Mathbb, Grp(F.Id("R"))), And(Lt(D(1), c), universal));
        return new Formula.Not(exists);
    }

    private static Formula ClaimFormula() => Disp(ClaimBody());
}
