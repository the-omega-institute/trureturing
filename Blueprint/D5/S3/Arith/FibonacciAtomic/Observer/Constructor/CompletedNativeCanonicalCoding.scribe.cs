using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;
internal sealed class CompletedNativeCanonicalCodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CompletedNativeCanonicalCoding", H("Canonical coding of the native completion"), Blocks(
            Describe.Lean(DescribeId.Create("completed-native-canonical-coding"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/CompletedNativeCanonicalCoding.canonical_coding"),
                H("Maximal atomic collapse and independent expansion are inverse"),
                Statement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The native domain is the existing unrestricted CompletionTree, with equality at every finite address, its actual substitution rho, its finite atomic iterates and its actual leafless Omega. Code is the unrestricted final coalgebra with natural-number leaves and ordered binary branches. In particular it includes nonregular infinite trees and arbitrary mixtures of finite leaves and leafless subtrees. codeOmega is the all-branch value, not a separate leaf label.")),
                    Paragraph(Text("Reduced excludes the atomic sibling collision ([n+1],[n]) at every reached address. Since fork codeOmega codeOmega equals codeOmega extensionally, the second collision has no retained pair distinct from that value. The final clause states this exclusion explicitly. Collapse tests whether the entire encountered native subtree is atomic before descending, so primitive occurrences are precisely maximal finite atomic subtrees. At every other native pair, both children and their order are retained.")),
                    Paragraph(Text("Expansion is an independent total corecursor: primitive n expands to the existing atomic n, while code branches expand to native ordered branches. Its additional native state copies finite atomic expansions without using collapse or a chosen inverse. The theorem proves that collapse lands in Reduced, both inverse identities on the full indicated domains, injectivity and surjectivity onto all reduced codes, preservation of reduction under every natural shift, intertwining of every actual rho iterate with label addition, and exact uniqueness of the code of Omega.")),
                    Paragraph(Text("In the formula, rhoIterate(k,X) denotes (Function.iterate rho k) X, and Injective denotes Function.Injective. CompletionTree and Code retain their unrestricted native meanings.")),
                    Paragraph(Text("The arbitrary-code atomic reflection in the proof rules out a reduced branch expanding to a finite atom. The inverse identities use finite-address extensionality and the pinned final-coalgebra bisimulation principle. The theorem supplies a semantic representation, with no algorithm for deciding atomicity of arbitrary infinite inputs and no assertion of integer-code-prefix continuity. Its primary output is an unrestricted structural equivalence, rather than bounded enumeration, a checker, a numeric reduction or a certified finite instance. No external literature novelty is asserted."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource Statement()
    {
        var x = V("X");
        var c = V("C");
        var k = V("k");
        var n = V("n");
        var l = V("l");
        var r = V("r");
        var collapse = Call("collapse", x);
        return StatementSource.FromAuthor(Disp(And(
            All("X", V("CompletionTree"), And(Call("Reduced", collapse),
                EqOf(Call("expansion", collapse), x))),
            All("C", V("Code"), Imp(Call("Reduced", c),
                EqOf(Call("collapse", Call("expansion", c)), c))),
            And(Call("Injective", V("collapse")), All("C", V("Code"),
                Imp(Call("Reduced", c), Some("X", V("CompletionTree"),
                    EqOf(collapse, c))))),
            All("k", V("Nat"), All("C", V("Code"), Imp(Call("Reduced", c),
                Call("Reduced", Call("shift", k, c))))),
            All("k", V("Nat"), All("X", V("CompletionTree"),
                EqOf(Call("collapse", Call("rhoIterate", k, x)), Call("shift", k, collapse)))),
            All("C", V("Code"), Imp(Call("Reduced", c), IffOf(
                EqOf(Call("expansion", c), V("Omega")), EqOf(c, V("codeOmega"))))),
            All("n", V("Nat"), EqOf(Call("collapse", Call("atomic", n)), Call("primitive", n))),
            All("l", V("CompletionTree"), All("r", V("CompletionTree"),
                Imp(Not(Some("n", V("Nat"), EqOf(Call("node", l, r), Call("atomic", n)))),
                    EqOf(Call("collapse", Call("node", l, r)),
                        Call("fork", Call("collapse", l), Call("collapse", r)))))),
            All("l", V("Code"), All("r", V("Code"),
                Imp(NeOf(Call("fork", l, r), V("codeOmega")),
                    Not(And(EqOf(l, V("codeOmega")), EqOf(r, V("codeOmega"))))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. arguments]);
    private static Formula EqOf(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula NeOf(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula Imp(Formula left, Formula right) => Seq(Par(left), Sp, Implies, Sp, Par(right));
    private static Formula IffOf(Formula left, Formula right) => Seq(Par(left), Sp, Iff, Sp, Par(right));
    private static Formula Not(Formula value) => Seq(Neg, Par(value));
    private static Formula And(params Formula[] values) =>
        Seq(values.Select((value, index) => index == 0 ? Par(value) : Seq(Sp, Land, Sp, Par(value))).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
}
