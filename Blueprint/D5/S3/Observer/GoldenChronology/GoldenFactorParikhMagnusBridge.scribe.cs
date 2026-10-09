using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenChronology;

internal sealed class GoldenFactorParikhMagnusBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual binary Parikh matrix and represented step-two Chen signature determine a legal golden factor. Their first-degree entries supply length and counts; one central Magnus coordinate supplies the remaining second-order information.",
        H("Golden factors through Parikh and Magnus coordinates"),
        Blocks(
            Paragraph(Text("Write W(n,i) for goldenFactor(n,i), R(i,n) for goldenWindowTrueCount(i,n), and B(i,n) for goldenTrueFalseCount(i,n). Write K(w) for scatteredTrueFalseCount(w), P(w) for binaryParikhMatrix(w), S(w) for chronologicalSignature(binaryLetterObservation,w), and C(w) for doubledMagnusDegreeTwo(S(w))(0,2). All lengths and starts are arbitrary naturals, and integer denotes the natural-to-integer cast.")),
            Describe.Lean(DescribeId.Create("actual-count"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/GoldenPalindromicFactorComplexity.goldenFactor_count_true"),
                H("The word's actual true count"), StatementSource.FromAuthor(CountFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The consecutive factor is the list of letters goldenWord(i+k) for k less than n. Counting its true letters gives exactly the canonical window count R(i,n). The false count is n minus R(i,n), because the two letter counts exhaust the length."))),
                DescribeRole.Theorem),
            Node("actual-pairs", "The word's actual scattered-pair count", "golden_factor_scattered_count", CountFormula(true),
                "Appending the letter at i+n extends W(n,i) to W(n+1,i). A false letter contributes R(i,n) new ordered pairs and a true letter contributes none. Thus the arbitrary-word pair counter K agrees with the golden sum B at every length, including zero."),
            Node("golden-center", "The division-free golden center", "golden_factor_doubled_magnus_center", CenterFormula(),
                "Substituting the actual word counts and pair count into the binary Magnus formula gives the displayed integer coordinate. The subtraction n minus R is performed in the integers after casting. The identity requires no positive-length or mixed-letter hypothesis."),
            Node("parikh-faithfulness", "The Parikh matrix has exactly the word's fibers", "golden_factor_eq_iff_parikh_matrix_eq", EquivalenceFormula(false),
                "Equality of the matrices gives equality of both letter counts and of K. Summing the two counts recovers n=m, and the fixed-length binomial recovery theorem then recovers the complete word. The reverse implication follows by substituting equal words. The lengths n and m need not be assumed equal."),
            Node("first-center-recovery", "First degree and center recover the word", "golden_factor_eq_of_first_degree_and_magnus", RecoveryFormula(),
                "Equality of the entire degreeOne matrices gives equality of their true and false entries. Together with equality of the one central doubled Magnus entry, it gives equal Parikh matrices and hence equal legal factors. Equality of the center alone is not the hypothesis here."),
            Node("chen-faithfulness", "The represented Chen signature has the same kernel", "golden_factor_eq_iff_step_two_signature_eq", EquivalenceFormula(true),
                "Equal signatures give equal first degree and equal center, so they give equal legal words. Equal words give equal signatures. These equivalences apply to word content, including the empty factor and pure-letter factors; they do not identify occurrence starts or attach prime labels to positions.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Nat(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), F.Id("Nat"), body);
    private static Formula Four(Formula body) => Nat("n", Nat("m", Nat("i", Nat("j", body))));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Integer(Formula n) => Call("integer", n);
    private static Formula Word(Formula n, Formula i) => Call("W", n, i);

    private static Formula CountFormula(bool pairs)
    {
        Formula n = F.Id("n"), i = F.Id("i"), w = Word(n, i);
        return Disp(Nat("n", Nat("i", Equal(pairs ? Call("K", w) : Call("count", w, F.Id("true")),
            Call(pairs ? "B" : "R", i, n)))));
    }

    private static Formula CenterFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), r = Integer(Call("R", i, n));
        return Disp(Nat("n", Nat("i", Equal(Call("C", Word(n, i)),
            Sub(Mul(D(2), Integer(Call("B", i, n))), Mul(r, Sub(Integer(n), r)))))));
    }

    private static Formula EquivalenceFormula(bool chen)
    {
        Formula a = Word(F.Id("n"), F.Id("i")), b = Word(F.Id("m"), F.Id("j"));
        return Disp(Four(Equivalent(Equal(a, b), Equal(Call(chen ? "S" : "P", a), Call(chen ? "S" : "P", b)))));
    }

    private static Formula RecoveryFormula()
    {
        Formula a = Word(F.Id("n"), F.Id("i")), b = Word(F.Id("m"), F.Id("j"));
        return Disp(Four(Implies(Equal(Call("degreeOne", Call("S", a)), Call("degreeOne", Call("S", b))),
            Implies(Equal(Call("C", a), Call("C", b)), Equal(a, b)))));
    }
}
