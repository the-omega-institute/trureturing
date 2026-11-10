using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class FactorialProductNonuniqueDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/FactorialProductNonunique.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/aivazidis2023commontransversal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The products of n!/n^n do not uniquely determine a finite set of distinct integers greater than one.",
        H("Nonuniqueness of factorial-weight products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factorial-product-uniqueness-claim"),
                DeclarationHandle.Create(Owner + "claim"), H("The unrestricted set assertion"),
                StatementSource.FromAuthor(Disp(Eq(F.Id("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Problem 5.6 of Aivazidis, Loukaki and Müller asks whether equal finite "
                    + "products of f(m)=Gamma(m+1)/m^m force the same distinct integer parameters "
                    + "after reordering. For integers m greater than one, f(m)=m!/m^m. "
                    + "The claim quantifies every two finite sets of natural numbers whose "
                    + "members exceed one. It imposes no bound, equal-cardinality hypothesis, "
                    + "prime restriction or group realization. The function orbitWeight is "
                    + "the original rational factorial-weight definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("factorial-product-uniqueness-refuted"),
                DeclarationHandle.Create(Owner + "result"), H("Two disjoint sets with equal products"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Open, ClaimBody(), Close))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take A={10,17,21,23,24,27,38,45,46,48,56,65,68,77,80,84,95,141} "
                        + "and B={11,16,20,22,25,26,39,44,47,49,57,64,69,76,81,85,94,140}. "
                        + "Both sets have eighteen elements, they are disjoint, and every "
                        + "member is greater than one. Their factorial-weight products are "
                        + "equal as exact rational numbers. Since ten belongs to A and not B, "
                        + "the equality cannot arise from reordering the parameters.")),
                    Paragraph(Text(
                        "The equality can also be understood using adjacent pairs: "
                        + "f(n+1)/f(n)=(n/(n+1))^n. The products of these ratios agree for "
                        + "the starting sets {16,20,22,26,44,64,76,94,140} and "
                        + "{10,24,38,46,48,56,68,80,84}. The pairs have distinct even starts "
                        + "and hence no common endpoints. Crossing numerators and denominators "
                        + "gives precisely A and B. The proof checks the displayed factorial "
                        + "products directly in rational arithmetic; no approximation enters.")),
                    Paragraph(Text(
                        "This refutes the full unrestricted uniqueness assertion, including "
                        + "the interpretation requiring all parameters on both sides to be "
                        + "distinct. It does not refute Theorem 4.6, whose parameters are primes. "
                        + "No minimality, composite-only strengthening or worldwide priority "
                        + "claim is asserted."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alm2024-factorial-product-uniqueness"),
                    ResolutionKind.Refuted)))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula AboveOne(Formula a) => All("m", Nat(), Imp(
        new Formula.Relation(F.Id("m"), FormulaRelationOperator.MemberOf, a),
        new Formula.Relation(D(1), FormulaRelationOperator.LessThan, F.Id("m"))));
    private static Formula Product(Formula a) => Seq(new Formula.Subscript(Prod,
        new Formula.Relation(F.Id("m"), FormulaRelationOperator.MemberOf, a)),
        Call("orbitWeight", F.Id("m")));
    private static Formula ClaimBody()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        return All("A", Call("Finset", Nat()), All("B", Call("Finset", Nat()),
            Imp(AboveOne(a), Imp(AboveOne(b), Imp(Eq(Product(a), Product(b)), Eq(a, b))))));
    }
}
