using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes;

internal sealed class AKMPUniformPrefixDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Palindromes/AKMPUniformPrefix";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/ambrozetal2019palindromiclength");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For k at least one, every proper prefix of either level-k image has palindromic length at most k+1.",
        H("Uniform prefix bound for the AKMP substitution"),
        Blocks(
            Paragraph(Text(
                "The alphabet is Bool, with a represented by true and b by false. "
                + "Section 4 of Ambroz, Kadlec, Masakova and Pelantova specifies the substitution "
                + "a to ababa and b to aba. Palindromic length uses the existing minimum number "
                + "of nonempty palindrome factors; the empty word has length zero.")),
            Describe.Lean(
                DescribeId.Create("akmp-psi-letter"),
                DeclarationHandle.Create(Module + ".psiLetter"), H("Letter images"),
                StatementSource.FromAuthor(Disp(And(
                    Equal(Call("psiLetter", F.Id("true")),
                        Seq(OpenBracket, F.Id("true"), Comma, F.Id("false"), Comma,
                            F.Id("true"), Comma, F.Id("false"), Comma, F.Id("true"), CloseBracket)),
                    Equal(Call("psiLetter", F.Id("false")),
                        Seq(OpenBracket, F.Id("true"), Comma, F.Id("false"), Comma,
                            F.Id("true"), CloseBracket))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Both images are nonempty palindromes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("akmp-psi-end"),
                DeclarationHandle.Create(Module + ".psiEnd"), H("Free-monoid substitution"),
                StatementSource.FromAuthor(Disp(Equal(F.Id("psiEnd"),
                    Call("lift", Seq(F.Id("c"), Sp, Mapsto, Sp,
                        Call("ofList", Call("psiLetter", F.Id("c")))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "FreeMonoid.lift extends the letter map multiplicatively. Multiplication "
                    + "in the free monoid is concatenation, so powers of psiEnd are actual "
                    + "iterations of this substitution."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("akmp-iterate-word"),
                DeclarationHandle.Create(Module + ".W"), H("Iterated letter image"),
                StatementSource.FromAuthor(Disp(All("k", Naturals(), All("c", F.Id("Bool"),
                    Equal(Call("W", F.Id("k"), F.Id("c")),
                        Call("toList", new Formula.Apply(
                            new Formula.Power(F.Id("psiEnd"), F.Id("k")),
                            [Call("of", F.Id("c"))]))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The zeroth image is the singleton origin. If A and B are the images of "
                    + "a and b at one level, the next images are ABABA and ABA."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("akmp-uniform-prefix-pl"),
                DeclarationHandle.Create(Module + ".uniform_prefix_pl"),
                H("Uniform proper-prefix bound"),
                StatementSource.FromAuthor(Disp(All("k", Naturals(),
                    Implies(AtMost(D(1), F.Id("k")), All("c", F.Id("Bool"),
                        All("m", Naturals(), Implies(
                            Less(F.Id("m"), Call("length", Call("W", F.Id("k"), F.Id("c")))),
                            AtMost(Call("PL", Call("take", F.Id("m"),
                                    Call("W", F.Id("k"), F.Id("c")))),
                                Add(F.Id("k"), D(1)))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "A simultaneous induction keeps both images nonempty and palindromic "
                        + "and supplies decompositions for every cut, including complete images. "
                        + "Write a and b for the lengths of A and B. The cuts of ABABA lie in "
                        + "five consecutive intervals, with endpoints a, a+b, 2a+b, "
                        + "2a+2b and 3a+2b. The first interval inherits an A-prefix decomposition; "
                        + "the second adds A to a B-prefix decomposition; the fourth adds ABA "
                        + "to a B-prefix decomposition.")),
                    Paragraph(Text(
                        "For the third interval put r=2a+b-m and D=A.drop r. A decomposition "
                        + "of A.take r followed by the single palindrome formed by D, B and the reverse of D "
                        + "gives the required prefix. In the fifth interval use r=3a+2b-m "
                        + "and the single palindrome formed by D, B, A, B and the reverse of D. Each "
                        + "added reflected factor is nonempty because B is nonempty. Reversing these factors "
                        + "uses the palindromicity of A and B. The take/drop identities recover "
                        + "the exact prefix. Each step adds at most one factor. Prefixes of ABA "
                        + "are prefixes of the initial ABA block of ABABA, so the same "
                        + "decompositions cover the second origin.")),
                    Paragraph(Text(
                        "The final decomposition bounds the existing minimum through Nat.find. "
                        + "This result concerns finite psi-iterate prefixes. It supplies no "
                        + "all-factor language transport, logarithmic asymptotic bound or "
                        + "matching lower bound for the Fibonacci word."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable),
            domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
