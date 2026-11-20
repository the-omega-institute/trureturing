using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.FreeGroup;

internal sealed class PrimeQuotientSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonidentity free-group element survives in a finite p-group quotient for every prime p.",
        H("Free groups are residually p for every prime"),
        Blocks(Describe.Lean(
            DescribeId.Create("normal-finite-prime-quotient-separation"),
            DeclarationHandle.Create(
                "D5/S3/FiniteGroups/FreeGroup/PrimeQuotientSeparation."
                    + "exists_normal_is_p_group_quotient_not_mem"),
            H("A normal subgroup separating a prescribed word"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026freegroupresidualp")),
            Blocks(
                Paragraph(Text(
                    "For every universe u, alphabet X in Type u, prime natural number p, "
                        + "and element w of FreeGroup X with w distinct from the identity, "
                        + "there exists a normal subgroup N of finite index excluding w "
                        + "such that FreeGroup X modulo N is a p-group. The alphabet may "
                        + "be infinite and need not be countable or have decidable equality. "
                        + "An empty alphabet is included: its free group has no nonidentity "
                        + "element, so the hypothesis on w excludes that case.")),
                Paragraph(Text(
                    "Express w as a normal syllable product x_1 raised to e_1 through "
                        + "x_k raised to e_k, where each integer exponent is nonzero and "
                        + "adjacent letters differ. Give syllable i a run of length "
                        + "p raised to v_p(e_i), and let D be the sum of these lengths. "
                        + "For each x in the entire alphabet, its shift matrix has entry "
                        + "one at (a,b) precisely when b=a+1 and the letter at column b "
                        + "is x. Sending every generator x to one plus this shift gives "
                        + "a homomorphism into the existing upper unitriangular subgroup "
                        + "of the special linear group over ZMod p, in dimension n=D+1.")),
                Paragraph(Text(
                    "The upper-entry coordinates have q=n(n-1)/2 free coordinates, "
                        + "so this finite group has cardinality p raised to q. Its "
                        + "elements therefore have period dividing p raised to K, "
                        + "where K=q+n. Reduce every signed exponent modulo p raised "
                        + "to K and take the nonnegative natural representative. This "
                        + "includes negative exponents and exponents divisible by p.")),
                Paragraph(Text(
                    "A power of one plus a shift has binomial entries along constant "
                        + "letter intervals. The first-row invariant says that after "
                        + "a prefix of total weight L the row vanishes beyond column L "
                        + "and is nonzero at L. Adjacent distinct letters make each "
                        + "run maximal at both ends. In the next run the sole possible "
                        + "contribution to the terminal entry comes from column L. "
                        + "The inequality p raised to v_p(e) at most D implies "
                        + "v_p(e)<K; Lucas congruences then show that the relevant "
                        + "binomial coefficient is nonzero modulo p. The invariant "
                        + "reaches column D. Since D is positive, this nonzero (0,D) "
                        + "entry distinguishes the image of w from the identity.")),
                Paragraph(Text(
                    "Take N to be the kernel of this homomorphism. Its finite image "
                        + "gives finite index, and the quotient embeds in the finite "
                        + "p-group through the kernel lift. Surjectivity onto the full "
                        + "unitriangular group is unnecessary. The separating quotient "
                        + "depends on the chosen word and prime. There is no fixed "
                        + "observation budget, executable inverse, or resource guarantee.")),
                Paragraph(Text(
                    "The syllable normalization, valuation-binomial argument, and "
                        + "first-row induction are adapted from the Tau Ceti contributors' "
                        + "immutable source identified in the Library note. The carrier "
                        + "and period use the existing upper-entry chart and cardinality "
                        + "theorems. The source attests the formal mathematical statement; "
                        + "Magnus and Iwasawa are cited there, but their primary papers "
                        + "are not used as independently read sources here."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula universe = F.Id("u");
        Formula alphabet = F.Id("X");
        Formula prime = F.Id("p");
        Formula word = F.Id("w");
        Formula subgroup = F.Id("N");
        Formula Qualified(string owner, string member) =>
            F.Seq(F.Id(owner), F.Dot, F.Id(member));
        Formula Apply(Formula function, params Formula[] arguments) =>
            new Formula.Apply(function, [.. arguments]);
        Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
            new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);
        Formula All(string name, Formula domain, Formula body) =>
            Bind(FormulaQuantifier.ForAll, name, domain, body);
        Formula Exists(string name, Formula domain, Formula body) =>
            Bind(FormulaQuantifier.Exists, name, domain, body);
        Formula And(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right);

        Formula freeGroup = Call("FreeGroup", alphabet);
        Formula quotient = Apply(Qualified("HasQuotient", "Quotient"), freeGroup, subgroup);
        Formula nonidentity = new Formula.Not(
            new Formula.Relation(word, FormulaRelationOperator.Equal, D(1)));
        Formula conclusion = Exists("N", Call("Subgroup", freeGroup),
            Exists("instNormal", Apply(Qualified("Subgroup", "Normal"), subgroup),
                And(Apply(Qualified("Subgroup", "FiniteIndex"), subgroup),
                    And(Call("IsPGroup", prime, quotient),
                        new Formula.Not(Apply(Qualified("Membership", "mem"), subgroup, word))))));

        return F.Disp(All("u", F.Id("UniverseLevel"),
            All("X", Apply(F.Id("Type"), universe),
                All("p", F.Id("Nat"),
                    All("instPrime", Call("Fact", Apply(Qualified("Nat", "Prime"), prime)),
                        All("w", freeGroup, All("hw", nonidentity, conclusion)))))));
    }
}
