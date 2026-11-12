using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class KimberlingA288476LengthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/KimberlingA288476Length.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Rewriting/kimberling2017a288476");
    private const string Quote = "Conjecture:  a(n) is the number of letters (0's and 1's) in the n-th iteration of the mapping 00->0101, 1->011, starting with 00; see A288473.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every native replacement-iterate length is the integer recurrence sequence of OEIS A288476.",
        H("Kimberling's replacement-iterate length conjecture"),
        Blocks(
            Paragraph(Text("The binary alphabet is Bool, with false representing 0 and true representing 1. Each pass reads the original input from left to right, consumes a matched block, and appends its replacement. Newly emitted output is scanned only on the next pass. The index starts at zero and includes both parities.")),
            Node("sourceScan", "The native replacement pass", ScanBody(),
                "The source operation is the StringReplace program in OEIS A288473. The displayed cases are disjoint: an empty input, a leading 00, a leading 1, a final unmatched 0, or a leading 01. In the last case the first 0 is retained and scanning resumes at the original 1. The recurrence calls are on the remaining original input, never the emitted replacement.", AssessedProvenance.FromLiterature(Source)),
            Node("sourceIter", "The source iterates",
                All("n", Nat(), Eqn(Call("sourceIter", V("n")),
                    Call("Function.iterate", V("sourceScan"), V("n"), Bits(false, false)))),
                "The initial word is 00. Function.iterate applies the native pass exactly n times, including the identity pass at zero.", AssessedProvenance.FromLiterature(Source)),
            Node("recurrence", "The independent integer recurrence",
                Eqn(V("recurrence"), Call("LinearRecurrence.mk", D(3), Seq(Bang, OpenBracket, Minus, D(2), Comma, D(4), Comma, D(1), CloseBracket))),
                "OEIS A288476 defines a(n) = a(n-1) + 4*a(n-2) - 2*a(n-3), with a(0)=2, a(1)=4, a(2)=8. The coefficient vector is indexed in ascending order: -2, 4, 1. Its coefficient type is Int, so subtraction is integer subtraction.", AssessedProvenance.FromLiterature(Source)),
            Node("recurrenceSeq", "The OEIS sequence",
                Eqn(V("recurrenceSeq"), Call("LinearRecurrence.mkSol", V("recurrence"),
                    Seq(Bang, OpenBracket, D(2), Comma, D(4), Comma, D(8), CloseBracket))),
                "Mathlib's mkSol constructs the sequence from the recurrence and its initial values. This definition contains no word, scanner or coding assumption.", AssessedProvenance.FromLiterature(Source)),
            Node("result", "Every iterate has the conjectured length",
                All("n", Nat(), Eqn(Seq(Open, Call("List.length", Call("sourceIter", V("n"))), Colon, V("Int"), Close), Call("recurrenceSeq", V("n")))),
                "OEIS A288476, COMMENTS: " + Quote
                + " The proof uses the auxiliary code D=00, E=01, O=1 and substitution D->EE, E->DOO, O->EO. For each code letter and every binary suffix, scanning its code followed by the suffix gives its substituted code followed by the scan of the suffix. List.foldr_hom extends this boundary identity to every finite code word. Function.Semiconj.iterate_right transports it to every source iterate. The existing image_add, image_one and subst_append give integer length states A(n+1)=2B(n), B(n+1)=A(n)+2C(n), C(n+1)=B(n)+C(n). Eliminating B and C gives A(n+3)=A(n+2)+4A(n+1)-2A(n). Mathlib's LinearRecurrence.eq_mk_of_is_sol_of_eq_init then identifies the native lengths with the independent sequence using initial values 2,4,8. No finite cutoff, parity condition or limiting-word assertion occurs.",
                AssessedProvenance.FromRepo(Source), true,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a288476-replacement-iterate-length"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, bool theorem = false, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("kimberling288476-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Word() => Call("List", V("Bool"));
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = name.Split('.');
        return parts.Length == 1
            ? new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args])
            : new Formula.Apply(Seq(Operatorname, Grp(V(parts[0])), Dot, Operatorname, Grp(V(parts[1]))), [.. args]);
    }
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Append(Formula a, Formula b) => Seq(a, Sp, Plus, Plus, Sp, b);
    private static Formula Cons(bool b, Formula tail) => Seq(V(b ? "true" : "false"), Sp, Colon, Colon, Sp, tail);
    private static Formula Bits(params bool[] bits)
    {
        var xs = new System.Collections.Generic.List<Formula> { OpenBracket };
        for (var i = 0; i < bits.Length; ++i) { if (i > 0) xs.Add(Comma); xs.Add(V(bits[i] ? "true" : "false")); }
        xs.Add(CloseBracket);
        return Seq([.. xs]);
    }
    private static Formula ScanBody() => new Formula.Aligned([
        Eqn(Call("sourceScan", Bits()), Bits()),
        All("v", Word(), Eqn(Call("sourceScan", Cons(false, Cons(false, V("v")))), Append(Bits(false, true, false, true), Call("sourceScan", V("v"))))),
        All("v", Word(), Eqn(Call("sourceScan", Cons(true, V("v"))), Append(Bits(false, true, true), Call("sourceScan", V("v"))))),
        Eqn(Call("sourceScan", Bits(false)), Bits(false)),
        All("v", Word(), Eqn(Call("sourceScan", Cons(false, Cons(true, V("v")))), Cons(false, Call("sourceScan", Cons(true, V("v"))))))
    ]);
}
