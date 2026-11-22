using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NormalityDegree;

internal sealed class TarnauceanuRationalRealizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/tarnauceanu2017normalitydegree");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every rational in (0, 1] is the normality degree of a finite group.",
        H("Tărnăuceanu's rational normality-degree conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tarnauceanu-normal-subgroups"),
                Handle("NormalSubgroups"),
                H("Normal subgroups"),
                StatementSource.FromAuthor(NormalSubgroups()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The subtype consists of all subgroups H whose normality predicate holds. "
                    + "It contains both the trivial subgroup and the whole group, counted once "
                    + "when they coincide."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tarnauceanu-normality-degree"),
                Handle("ndeg"),
                H("Normality degree"),
                StatementSource.FromAuthor(NormalityDegree()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The denominator latticeCount G is Nat.card (Subgroup G), the cardinality "
                    + "of the full subgroup lattice. Both cardinalities are cast to the rationals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tarnauceanu-normality-degree-claim"),
                Handle("claim"),
                H("Conjecture 4.1"),
                StatementSource.FromAuthor(Claim()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Conjecture 4.1 of the journal article, numbered Conjecture 4.4 in the preprint, "
                    + "asks for every rational x with 0 < x ≤ 1 an actual finite group of degree x. "
                    + "The existential witnesses supply the carrier, its group operation and laws, "
                    + "and a proof of finiteness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tarnauceanu-normality-degree-result"),
                Handle("result"),
                H("Exact rational attainment"),
                StatementSource.FromAuthor(Claim()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For x = 1, use the cyclic group of order two. In a commutative group "
                        + "every subgroup is normal, so the two cardinalities agree and are positive.")),
                    Paragraph(Text(
                        "For 0 < x < 1, write x = u/v with 0 < u < v. Put d = v − u and t = 2d. "
                        + "Choose a prime p > 2t congruent to 1 modulo 2^t, and put "
                        + "B = pu + d − 1. Then t ≤ B. A unit modulo p of order 2^t gives an "
                        + "automorphism of the prime cyclic group of the same order. Sending the "
                        + "generator of the cyclic group of order 2^B to that automorphism forms "
                        + "the action of the semidirect product.")),
                    Paragraph(Text(
                        "At every quotient level j = 0 through B, the subgroup containing "
                        + "the prime kernel is the inverse image of the level. It is normal. "
                        + "For j ≤ B − t, the action on the level is trivial and the standard "
                        + "section is the unique subgroup at that level meeting the kernel "
                        + "trivially. It is normal. For j > B − t, exactly p conjugate sections "
                        + "meet the kernel trivially. The generator acts without nonidentity "
                        + "fixed points on the prime kernel, so distinct kernel elements give "
                        + "distinct sections and conjugation by the kernel moves each section.")),
                    Paragraph(Text(
                        "The resulting counts on the same group are 2B − t + 2 normal subgroups "
                        + "and 2B − t + 2 + pt subgroups in total. The counts agree with the "
                        + "specialization of the published ZM formula. Substituting B and t gives "
                        + "2pu and 2pv, so their ratio is exactly u/v."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tarnauceanu-2017-normality-degree-rational-attainment"),
                    ResolutionKind.Proved)))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Module + "." + name);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.BindMany(quantifier,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, type, body);

    private static Formula Imp(Formula premise, Formula body) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, body);

    private static Formula Instance(string name, Formula g) =>
        Seq(OpenBracket, Call(name, g), CloseBracket);

    private static Formula NormalSubgroups()
    {
        var g = F.Id("G");
        var h = F.Id("H");
        var subtype = Seq(OpenBrace, h, Sp, Colon, Sp, Call("Subgroup", g), Sp, Mid, Sp,
            h, Dot, F.Id("Normal"), CloseBrace);
        return Disp(All("G", F.Id("Type"), Seq(Instance("Group", g), Sp,
            Call("NormalSubgroups", g), Sp, Eq, Sp, subtype)));
    }

    private static Formula NormalityDegree()
    {
        var g = F.Id("G");
        var card = new Formula.Apply(Seq(Operatorname, Grp(Seq(F.Id("Nat"), Dot, F.Id("card")))),
            [Call("NormalSubgroups", g)]);
        var ratio = new Formula.Fraction(card, Call("latticeCount", g));
        return Disp(All("G", F.Id("Type"), Seq(Instance("Group", g), Sp, Instance("Finite", g), Sp,
            Call("ndeg", g), Sp, Eq, Sp, ratio)));
    }

    private static Formula Claim()
    {
        var x = F.Id("x");
        var g = F.Id("G");
        var group = F.Id("group");
        var finite = F.Id("finite");
        var degree = new Formula.Apply(F.Id("ndeg"), [g, group, finite]);
        var equal = Seq(degree, Sp, Eq, Sp, x);
        return Disp(All("x", Seq(Mathbb, Grp(F.Id("Q"))),
            Imp(Seq(D(0), Lt, x), Imp(Seq(x, Le, D(1)),
                Exists("G", F.Id("Type"), Exists("group", Call("Group", g),
                    Exists("finite", Call("Finite", g), equal)))))));
    }
}
