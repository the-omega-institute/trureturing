using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ErdosDeepTripleClassificationRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/dukesgaede2023erdosdeep");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three progressions in the integers modulo twenty-seven fall outside the conjectured list.",
        H("The Conjectured Classification of Erdos-Deep Triples Is Incomplete"),
        Blocks(
            Node("cyclic-distance-definition", "Distance in a cyclic group", "cdist",
                CdistFormula(),
                "Section 1 of the source measures distance in the integers modulo n by "
                    + "the smaller of the two arc lengths, writing the norm of x as the "
                    + "minimum of x and its negative, each reduced below n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("progression-definition", "A modular arithmetic progression", "apList",
                ApListFormula(),
                "The source writes AP(n, g, k) for the progression with k terms, first term "
                    + "zero and common difference g, read inside the integers modulo n. The "
                    + "terms need not be distinct for every g and k; the statement below asks "
                    + "for distinctness separately.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pair-distances-definition", "Distances inside one progression", "pairDists",
                PairDistsFormula(),
                "Every unordered pair of distinct points contributes one distance. A list of "
                    + "k points contributes k choose two of them.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("family-distances-definition", "Distances of a family of three", "familyDists",
                FamilyDistsFormula(),
                "The source takes the multiset union over the members of the family; distances "
                    + "between points of different members are not counted.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("multiplicities-definition", "The multiplicity of each distance that occurs",
                "multiplicities",
                MultiplicitiesFormula(),
                "One entry for each distinct distance, giving how many pairs realise it.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("erdos-deep-definition", "Erdos-deep families", "IsErdosDeep",
                IsErdosDeepFormula(),
                "Section 1 of the source reads: \"we say that F is Erdos-deep if the "
                    + "multiplicities of distances that occur in the distance multiset are "
                    + "precisely one, two, up to k minus one for some integer k.\" Writing m "
                    + "for the number of distinct distances, that says each of one through m "
                    + "occurs exactly once among the multiplicities; the integer k is then m "
                    + "plus one, and it satisfies k times k minus one equals the sum over the "
                    + "members of the family of the length times the length minus one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("allowed-definition", "The conjectured list of length triples", "allowed",
                AllowedFormula(),
                "The two triples the source expects for infinitely many moduli, followed by "
                    + "the thirteen it expects for finitely many.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("classification-statement", "The conjectured classification", "claim",
                ClaimFormula(),
                "Conjecture 1 of the source reads verbatim: \"An Erdos-deep family of three "
                    + "APs of lengths k1 at least k2 at least k3 in Z n exists if and only if "
                    + "the triple lies in the first set, each for infinitely many n, or in the "
                    + "second set, each for a finite number of values of n.\" The statement "
                    + "displayed here is the forward half, the one the witness below "
                    + "contradicts. It carries the conventions the source fixes for families "
                    + "of progressions, lengths at least three and the generators together "
                    + "with the modulus having greatest common divisor one, and in addition "
                    + "the bound on the longest length that the accompanying thesis states in "
                    + "its own version of the conjecture. Carrying that bound makes the "
                    + "statement stronger, so refuting it refutes the published form as well.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("classification-refuted", "The conjectured list is incomplete", "result",
                ResultFormula(),
                "In the integers modulo twenty-seven take the progressions with twelve, six "
                    + "and five terms and common differences one, twelve and seven. The first "
                    + "is zero through eleven and gives each distance from one to eleven the "
                    + "multiplicity twelve minus it. The second is zero, twelve, twenty-four, "
                    + "nine, twenty-one, six and gives three four times, six three times, nine "
                    + "three times and twelve five times. The third is zero, seven, fourteen, "
                    + "twenty-one, one and gives one once, six twice, seven four times and "
                    + "thirteen three times. The union gives thirteen distinct distances whose "
                    + "multiplicities are twelve, ten, thirteen, eight, seven, eleven, nine, "
                    + "four, six, two, one, five and three, that is each of one through "
                    + "thirteen exactly once, so the family is Erdos-deep. The lengths are at "
                    + "least three and decreasing, the modulus and the three differences have "
                    + "greatest common divisor one, and twelve is at most fourteen, the bound "
                    + "the thesis imposes. The triple twelve, six, five is in neither part of "
                    + "the conjectured list.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("erdos-deep-triple-classification-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula CdistFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x"), y = F.Id("y");
        Formula d = Call("mod", Subtract(Add(x, n), y), n);
        return Disp(Universal("n", Naturals(),
            Universal("x", Naturals(),
                Universal("y", Naturals(),
                    Equal(Call("cdist", n, x, y), Call("min", d, Subtract(n, d)))))));
    }

    private static Formula ApListFormula()
    {
        Formula n = F.Id("n"), g = F.Id("g"), k = F.Id("k"), i = F.Id("i");
        Formula rule = Seq(i, Sp, Mapsto, Sp, Call("mod", Multiply(i, g), n));
        return Disp(Universal("n", Naturals(),
            Universal("g", Naturals(),
                Universal("k", Naturals(),
                    Equal(Call("apList", n, g, k),
                        Call("map", rule, Call("range", k)))))));
    }

    private static Formula PairDistsFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x"), l = F.Id("l");
        Formula basis = Equal(Call("pairDists", n, Nil()), Nil());
        Formula recursion = Equal(Call("pairDists", n, Cons(x, l)),
            Call("append", Call("map", Call("cdist", n, x), l), Call("pairDists", n, l)));
        return Disp(Universal("n", Naturals(),
            Universal("x", Naturals(),
                Universal("l", ListOfNaturals(),
                    Seq(basis, Sp, Sp, Sp, recursion)))));
    }

    private static Formula FamilyDistsFormula()
    {
        Formula n = F.Id("n");
        Formula g1 = F.Id("g1"), g2 = F.Id("g2"), g3 = F.Id("g3");
        Formula k1 = F.Id("k1"), k2 = F.Id("k2"), k3 = F.Id("k3");
        Formula part(Formula g, Formula k) => Call("pairDists", n, Call("apList", n, g, k));
        return Disp(Equal(Call("familyDists", n, g1, g2, g3, k1, k2, k3),
            Call("append", part(g1, k1), Call("append", part(g2, k2), part(g3, k3)))));
    }

    private static Formula MultiplicitiesFormula()
    {
        Formula ds = F.Id("ds"), d = F.Id("d");
        Formula rule = Seq(d, Sp, Mapsto, Sp, Call("count", ds, d));
        return Disp(Universal("ds", ListOfNaturals(),
            Equal(Call("multiplicities", ds),
                Call("map", rule, Call("dedup", ds)))));
    }

    private static Formula IsErdosDeepFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), m = F.Id("m");
        Formula g1 = F.Id("g1"), g2 = F.Id("g2"), g3 = F.Id("g3");
        Formula k1 = F.Id("k1"), k2 = F.Id("k2"), k3 = F.Id("k3");
        Formula ms = Call("multiplicities", Call("familyDists", n, g1, g2, g3, k1, k2, k3));
        Formula body = And(Equal(m, Call("length", ms)),
            Universal("i", Naturals(),
                Implies(And(LessEqual(D(1), i), LessEqual(i, m)),
                    Equal(Call("count", ms, i), D(1)))));
        return Disp(Iff(Call("IsErdosDeep", n, g1, g2, g3, k1, k2, k3),
            Exists("m", Naturals(), body)));
    }

    private static Formula AllowedFormula() =>
        Disp(Seq(Call("allowed"), Sp, Eq, Sp, OpenBrace,
            Triple(D(4), D(4), D(3)), Comma, Sp, Triple(D(6), D(3), D(3)), Comma, Sp,
            Triple(D(6), D(5), D(3)), Comma, Sp, Triple(D(6), D(6), D(4)), Comma, Sp,
            Triple(D(6), D(6), D(6)), Comma, Sp, Triple(D(7), D(7), D(3)), Comma, Sp,
            Triple(D(9), D(4), D(3)), Comma, Sp, Triple(D(8), D(7), D(4)), Comma, Sp,
            Triple(D(8), D(8), D(5)), Comma, Sp, Triple(D(1, 0), D(6), D(4)), Comma, Sp,
            Triple(D(1, 2), D(4), D(4)), Comma, Sp, Triple(D(1, 3), D(5), D(3)), Comma, Sp,
            Triple(D(1, 3), D(7), D(4)), Comma, Sp, Triple(D(1, 6), D(5), D(4)), Comma, Sp,
            Triple(D(2, 1), D(6), D(4)), CloseBrace));

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula g1 = F.Id("g1"), g2 = F.Id("g2"), g3 = F.Id("g3");
        Formula k1 = F.Id("k1"), k2 = F.Id("k2"), k3 = F.Id("k3");
        Formula lengths = And(LessEqual(D(3), k3), And(LessEqual(k3, k2), LessEqual(k2, k1)));
        Formula bound = LessEqual(k1,
            Add(Call("div", n, Multiply(D(2), Call("gcd", n, g1))), D(1)));
        Formula coprime = Equal(Call("gcd", n, g1, g2, g3), D(1));
        Formula distinct = And(Call("Nodup", Call("apList", n, g1, k1)),
            And(Call("Nodup", Call("apList", n, g2, k2)),
                Call("Nodup", Call("apList", n, g3, k3))));
        Formula hypotheses = And(lengths, And(bound, And(coprime,
            And(distinct, Call("IsErdosDeep", n, g1, g2, g3, k1, k2, k3)))));
        Formula conclusion = Member(Triple(k1, k2, k3), Call("allowed"));
        Formula inner = Implies(hypotheses, conclusion);
        Formula b1 = Universal("k3", Naturals(), inner);
        Formula b2 = Universal("k2", Naturals(), b1);
        Formula b3 = Universal("k1", Naturals(), b2);
        Formula b4 = Universal("g3", Naturals(), b3);
        Formula b5 = Universal("g2", Naturals(), b4);
        Formula b6 = Universal("g1", Naturals(), b5);
        Formula body = Universal("n", Naturals(), b6);
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula ListOfNaturals() => Call("List", Naturals());

    private static Formula Nil() => Seq(OpenBracket, CloseBracket);

    private static Formula Cons(Formula head, Formula tail) =>
        Seq(head, Sp, Colon, Colon, Sp, tail);

    private static Formula Triple(Formula a, Formula b, Formula c) =>
        Seq(Open, a, Comma, Sp, b, Comma, Sp, c, Close);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Member(Formula element, Formula collection) =>
        Seq(element, Sp, InMacro, Sp, collection);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
