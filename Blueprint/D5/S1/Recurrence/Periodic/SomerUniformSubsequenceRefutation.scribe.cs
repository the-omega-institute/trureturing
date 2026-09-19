using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class SomerUniformSubsequenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/somerkrizek2025uniformsubsequence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A third-order integer recurrence refutes the proposed higher-order uniform-subsequence law.",
        H("A Counterexample to the Somer-Krizek Uniform-Subsequence Conjecture"),
        Blocks(
            Paragraph(Text(
                "Somer and Krizek define a k-th order integer recurrence with coefficients "
                    + "listed from the newest preceding term to the oldest. The formal recurrence "
                    + "therefore reverses that list for LinearRecurrence, whose coefficient at "
                    + "index i multiplies the term shifted by i.")),
            Node("paperRecurrence", "The paper-order recurrence",
                "The order is k and coefficient i is the reversed paper coefficient.",
                DescribeRole.Definition),
            Node("IsLeastPositivePeriodMod", "Least positive modular period",
                "The proposed period is positive, is a period after reduction modulo the modulus, "
                    + "and is at most every other positive modular period.",
                DescribeRole.Definition),
            Node("UniformCounts", "Uniform counts on a full period",
                "For every residue in Fin(modulus), exactly copies indices below modulus times "
                    + "copies reduce to that residue.", DescribeRole.Definition),
            Node("UniformSubsequenceCounts", "Uniform arithmetic-subsequence counts",
                "For every residue in Fin(modulus), exactly copies sampled values at "
                    + "start+n*step, for n below modulus times copies, reduce to that residue.",
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("somer-krizek-full-claim"),
                DeclarationHandle.Create(Prefix + "fullClaim"),
                H("Somer and Krizek's Conjecture 4.2"),
                StatementSource.FromAuthor(FullClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every order k at least two, every integer coefficient vector and every "
                        + "integer solution, the source hypotheses quantify over a prime p, an "
                        + "exponent e at least one and a positive E. They require the last paper "
                        + "coefficient to be coprime to p, exact least period p^e E, and E copies "
                        + "of every residue in that period. For every positive g coprime to p and "
                        + "every nonnegative start s, the conclusion requires E/gcd(g,E) copies "
                        + "of every residue in the prescribed sampled range."))),
                DescribeRole.Definition),
            Node("CertificateWord", "Six-code certificate words",
                "A certificate word assigns one code in Fin 5 to each of six positions.",
                DescribeRole.Definition),
            FormulaNode("actualWord", "The actual encoded period", ActualWordFormula(),
                "The codes (2,3,4,2,1,0) decode to the integer period (0,1,2,0,-1,-2).",
                DescribeRole.Definition),
            Node("decodeCode", "Decoding a finite code",
                "The natural value of a Fin 5 code is cast to the integers and shifted down by two.",
                DescribeRole.Definition),
            Node("sequenceOfWord", "The periodic integer sequence",
                "At index n, the word is read at n modulo six and its finite code is decoded.",
                DescribeRole.Definition),
            FormulaNode("actualCoefficients", "The third-order coefficients",
                ActualCoefficientsFormula(),
                "The paper-order coefficient vector is (0,0,-1), so the recurrence is "
                    + "w(n+3)=-w(n).", DescribeRole.Definition),
            Node("CounterexampleCertificate", "The complete counterexample certificate",
                "A certificate proves the all-index recurrence, exact least modular period six, "
                    + "two occurrences of every residue in the full orbit, and failure of the "
                    + "step-two sampled count.", DescribeRole.Definition),
            Node("RefutationEvidence", "Reusable refutation evidence",
                "The evidence package contains the actual complete certificate and the map from "
                    + "any such certificate to the negation of the full source claim.",
                DescribeRole.Definition),
            Node("actualRefutationEvidence", "The proved refutation evidence",
                "The private all-index proofs establish the actual certificate. Its refutation "
                    + "map instantiates every source quantifier at k=3, p=3, e=1, E=2, g=2 and "
                    + "s=0, then contradicts the sampled uniformity conclusion.",
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("somer-krizek-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Conjecture 4.2 is false"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The integer period is (0,1,2,0,-1,-2). It satisfies w(n+3)=-w(n) "
                        + "for every natural n. Modulo three, its least period is six and each "
                        + "residue occurs twice. With g=2 and s=0, E/gcd(g,E)=1 while the first "
                        + "three sampled residues are 0,2,2, so residue one occurs zero times. "
                        + "The retained let-bound actualWord is the same complete certificate "
                        + "used by the information readout."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string title, string text,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("somer-krizek-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static DocumentBlock.Describe FormulaNode(string declaration, string title,
        Formula formula, string text, DescribeRole role) => Describe.Lean(
            DescribeId.Create("somer-krizek-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static Formula FullClaimFormula()
    {
        var k = V("k");
        var a = V("a");
        var w = V("w");
        var p = V("p");
        var e = V("e");
        var copies = V("E");
        var g = V("g");
        var s = V("s");
        var modulus = Power(p, e);
        var conclusion = All("s", Naturals(),
            Call("UniformSubsequenceCounts", modulus,
                Divide(copies, Call("gcd", g, copies)), g, s, w));
        Formula statement = All("g", Naturals(),
            Imply(Less(D(0), g), Imply(Call("Coprime", g, p), conclusion)));
        statement = Imply(Call("UniformCounts", modulus, copies, w), statement);
        statement = Imply(
            Call("IsLeastPositivePeriodMod", modulus, w, Multiply(modulus, copies)),
            statement);
        statement = Imply(
            Equal(Call("gcd", Call("a", Subtract(k, D(1))), p), D(1)), statement);
        statement = Imply(Less(D(0), copies), statement);
        statement = Imply(LessEqual(D(1), e), statement);
        statement = Imply(Call("Prime", p), statement);
        statement = All("E", Naturals(), statement);
        statement = All("e", Naturals(), statement);
        statement = All("p", Naturals(), statement);
        statement = Imply(Call("IsSolution", Call("paperRecurrence", a), w), statement);
        statement = All("w", Arrow(Naturals(), Integers()), statement);
        statement = All("a", Arrow(Call("Fin", k), Integers()), statement);
        statement = All("k", Naturals(), Imply(LessEqual(D(2), k), statement));
        return Disp(Equal(V("fullClaim"), statement));
    }

    private static Formula ActualWordFormula() =>
        Disp(Equal(V("actualWord"), Tuple(D(2), D(3), D(4), D(2), D(1), D(0))));

    private static Formula ActualCoefficientsFormula() =>
        Disp(Equal(V("actualCoefficients"), Tuple(D(0), D(0), Seq(Minus, D(1)))));

    private static Formula ResultFormula() => Disp(Seq(
        Operatorname, Grp(V("let")), Open, V("counterexample"), Sp, Eq, Sp, V("actualWord"),
        Close, Semi, Sp, Neg, Sp, V("fullClaim")));

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Divide(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Slash, Sp, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Imply(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula LessEqual(Formula left, Formula right) => Seq(left, Sp, Le, Sp, right);
    private static Formula Multiply(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Cdot, Sp, Parenthesized(right));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Subtract(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Minus, Sp, Parenthesized(right));
    private static Formula Tuple(params Formula[] values)
    {
        var items = new List<Formula> { Open };
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(values[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }
    private static Formula V(string name) => F.Id(name);
}
