using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class A397436GeneralSupercongruenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/oeis2026a397436");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-factor positive instance refutes the unrestricted signed product congruence.",
        H("A397436 Conjecture 3: the unrestricted congruence is false"),
        Blocks(
            Node("U", "The inclusive signed binomial-product sum", UFormula(),
                "For natural r, m is a function Fin r to the integers. Ring.choose "
                + "is the generalized binomial on integer upper arguments, including "
                + "negative values. The sum includes k=0 and k=M*n; the product "
                + "runs over all r indices. NatCast embeds n into the integers before "
                + "multiplication by m(i). No zero-for-negative-upper convention is used.",
                DescribeRole.Definition),
            Node("claim", "The full same-r universal assertion", ClaimFormula(),
                "IntVector(r) means Fin r to the integers; Prime is natural primality. "
                + "The same positive r controls factor count, both lifting exponents "
                + "and the exponent 3*r of the modulus. NatSub is natural subtraction; "
                + "r>0 makes r-1 the source exponent. M is any positive natural and "
                + "m is unrestricted. This encodes the literal item 3, with no "
                + "restrictions imported from items 1 or 2.", DescribeRole.Definition),
            Node("result", "The universal assertion is false", Disp(new Formula.Not(F.Id("claim"))),
                "Set r=1, m(0)=1, M=1 and p=5. All domain conditions hold. "
                + "Ring.choose_natCast changes the single factor to Nat.choose. "
                + "The inclusive rows are [1,5,10,10,5,1] and [1,1], giving "
                + "U(5)=32 and U(1)=2. Their difference is 30; the required "
                + "modulus is 125 and does not divide 30. Instantiating the full "
                + "signed universal claim therefore gives a contradiction. The "
                + "proof is an application of existing binomial semantics and "
                + "finite arithmetic; its admission is the named external problem "
                + "resolution. This addresses only unrestricted Conjecture 3. "
                + "It makes no conclusion about Conjectures 1 or 2, the special "
                + "negative-parameter two-factor case, an unprinted restriction "
                + "or the author's intended relationship between factor and lift indices.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397436-general-supercongruence"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a397436-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula UFormula()
    {
        var summand = Product("i", Call("Fin", V("r")),
            Call("RingChoose", Mul(Call("m", V("i")), Call("NatCast", V("n"))), V("k")));
        var total = Sum("k", Call("Icc", D(0), Mul(V("M"), V("n"))), summand);
        var equality = Equal(Call("U", V("m"), V("M"), V("n")), total);
        var allN = ForAll("n", Naturals(), equality);
        var allM = ForAll("M", Naturals(), allN);
        var allVectors = ForAll("m", Call("IntVector", V("r")), allM);
        return Disp(ForAll("r", Naturals(), allVectors));
    }

    private static Formula ClaimFormula()
    {
        var high = Call("U", V("m"), V("M"), Pow(V("p"), V("r")));
        var low = Call("U", V("m"), V("M"), Pow(V("p"), Call("NatSub", V("r"), D(1))));
        var modulus = Pow(Call("NatCast", V("p")), Mul(D(3), V("r")));
        var divisibility = Call("Divides", modulus, Sub(high, low));
        var admissiblePrime = And(Call("Prime", V("p")), AtMost(D(5), V("p")));
        var allPrimes = ForAll("p", Naturals(), Implies(admissiblePrime, divisibility));
        var allM = ForAll("M", Naturals(), Implies(Less(D(0), V("M")), allPrimes));
        var allVectors = ForAll("m", Call("IntVector", V("r")), allM);
        return Disp(ForAll("r", Naturals(), Implies(Less(D(0), V("r")), allVectors)));
    }

    private static Formula V(string s) => F.Id(s);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Sum(string name, Formula range, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, range)), Sp, Grp(body));
    private static Formula Product(string name, Formula range, Formula body) =>
        Call("Product", V(name), range, body);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
