using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class SparseContinuationNontransitivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Automata/SparseContinuationNontransitivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-word promise has nontransitive agreement on common legal continuations.",
        H("Sparse continuation agreement need not be transitive"),
        Blocks(
            new DocumentBlock.Section(H("One finite input domain"), Blocks(
                Node("promise", "The three legal words", F.Disp(Equal(Id("promise"),
                    new Formula.SetLiteral([Word(2, 0), Word(3, 1), Word(4, 0)]))),
                    "Use the five-element alphabet Fin 5, with a, b, x, y, z represented by 0, 1, 2, 3, 4. "
                        + "A word is a List, read from left to right. The displayed set is the coercion of a finite set of three actual words. "
                        + "It is nonempty because it contains xa. Prefixes is the existing set of words with some legal right continuation.",
                    DescribeRole.Definition),
                Node("output", "The legal output labels", F.Disp(All("w", Id("promise"),
                    Equal(Call("output", Id("w")), Call("ite",
                        Equal(Call("val", Id("w")), Word(4, 0)), Num(1), Num(0))))),
                    "The output type is Fin 2. The labels of xa and yb are zero and the label of za is one. "
                        + "The output function accepts only a word of the promise subtype; words outside that domain have no prescribed output.",
                    DescribeRole.Definition))),
            new DocumentBlock.Section(H("Compatibility on common legal suffixes"), Blocks(
                new DocumentBlock.DisplayFormula(F.Disp(AgreementFormula())),
                Paragraph(Text(
                    "For prefixes u and v, agreement means equality of the prescribed outputs for every common legal suffix w. "
                        + "The membership proofs h and k make both output applications well typed. There is no requirement on a suffix legal at only one prefix. "
                        + "This is exactly the negation of the existing Conflict: on distinct prefixes it excludes every unequal-output continuation, "
                        + "and on the diagonal the two legal-word subtype values coincide. No outside-domain rejection value is added.")),
                Node("claim", "The transitivity assertion", F.Disp(Equal(Id("claim"),
                    All("u", PrefixType(), All("v", PrefixType(), All("t", PrefixType(),
                        Implies(NoConflict(Id("u"), Id("v")),
                            Implies(NoConflict(Id("v"), Id("t")), NoConflict(Id("u"), Id("t"))))))))),
                    "This assertion concerns the same three-word promise throughout. It says that two successive compatible pairs force the third pair to be compatible.",
                    DescribeRole.Definition),
                Node("result", "Failure of transitivity", F.Disp(Not(Id("claim"))),
                    "Take the actual prefixes x, y, z. If x followed by w is legal, constructor equality in the three-word domain forces w to be the one-letter word a. "
                        + "For y it forces w to be b, and for z it forces w to be a. Since a and b are distinct, x and y have no common legal suffix, and neither do y and z. "
                        + "Both pairs therefore agree vacuously. The suffix a is legal at x and z, where the outputs are respectively zero and one, giving an actual Conflict. "
                        + "Transitivity applied to the first two pairs contradicts this third pair. The empty suffix is illegal at each of x, y, z, and longer or other suffixes are excluded by the same constructor equalities. "
                        + "This is the known construction of Proposition 3.3 in the original computational behavior representation theory, rather than a new research counterexample.",
                    DescribeRole.Theorem)))),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Automata/PromiseColoringTotalization"))]));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("sparse-continuation-" + declaration),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Word(params long[] letters)
    {
        var items = new List<Formula> { F.OpenBracket };
        for (var i = 0; i < letters.Length; i++)
        {
            if (i > 0) items.AddRange([F.Comma, F.Sp]);
            items.Add(Num(letters[i]));
        }
        items.Add(F.CloseBracket);
        return F.Seq([.. items]);
    }

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Not(Formula body) => F.Seq(F.Neg, F.Open, body, F.Close);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula PrefixType() => Call("Prefixes", Id("promise"));
    private static Formula NoConflict(Formula left, Formula right) =>
        Not(Call("Conflict", Id("promise"), Id("output"), left, right));
    private static Formula Append(Formula word, Formula suffix) => Call("append", word, suffix);
    private static Formula Legal(Formula word) =>
        new Formula.Relation(word, FormulaRelationOperator.MemberOf, Id("promise"));

    private static Formula AgreementFormula()
    {
        Formula u = Id("u"), v = Id("v"), w = Id("w");
        var left = Append(Call("val", u), w);
        var right = Append(Call("val", v), w);
        var equal = Equal(Call("output", Call("Subtype", left, Id("h"))),
            Call("output", Call("Subtype", right, Id("k"))));
        return All("u", PrefixType(), All("v", PrefixType(),
            new Formula.Logic(NoConflict(u, v), FormulaLogicOperator.Iff,
                All("w", Call("List", Call("Fin", Num(5))),
                    All("h", Legal(left), All("k", Legal(right), equal))))));
    }
}
