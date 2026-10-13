using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class PureProgramQubitObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/QuantumChannels/PureProgramQubitObstruction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/gschwendtnerbluhmwinter2021programmability");
    private static readonly LibraryNoteRef Rigidity = LibraryNoteRef.Create("D5/L/QuantumChannels/braun2014universalqubitchannels");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three pure targets prevent a two-dimensional pure program register from producing a mixed qubit target.",
        H("A qubit pure-program obstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("gbw-channel"), DeclarationHandle.Create(Owner + "IsChannel"), H("Finite Kraus channels"),
                StatementSource.FromAuthor(Disp(ChannelFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("PDF p. 3: “A quantum channel is a completely positive trace-preserving map T : B(H₁) → B(H₂), where d₁, d₂ ∈ ℕ.” The finite Kraus convention represents such channels on complex Matrix carriers. A and B may be arbitrary finite types, so a processor's product index is included. ofKraus denotes the frozen MatrixMap.of_kraus, whose action is the sum Kᵢ rho (Kᵢ)ᴴ; conjTranspose is the matrix conjugate transpose. The completeness identity preserves trace. finite_kraus_quantum_channel states the related canonical QuantumChannel formulation on CStarMatrix; it is not on this module's dependency path."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gbw-four-replacements"), DeclarationHandle.Create(Owner + "no_four_replacements"), H("Four targets are incompatible"),
                StatementSource.FromAuthor(Disp(ObstructionFormula())), AssessedProvenance.FromLiterature(Rigidity),
                Blocks(Paragraph(Text("Braun, Giraud, Nechita, Pellegrini and Žnidarič, A universal set of qubit quantum channels, arXiv:1306.0495v2, Theorem IV.9, classify the pure outputs of qubit channels: three distinct pure outputs force unitary conjugation. Fixing a basis input of an exact processor gives a qubit channel from the program register to the output. In the GBW-5 covariant-program question, its three pure replacement targets therefore force every pure program output to be pure, excluding the fourth target, one half of the identity. The theorem here establishes a stronger algebraic formulation that does not require program normalization. The input dimension and the finite Kraus count are unrestricted. Fix the basis input Matrix.single x x 1. The program-to-output map is linear, and its Gram matrix is the processor output. The first two targets force independent program vectors with opposite zero rows. The third target forces their nonzero environment rows to be parallel. Every program image then has dependent rows, whereas one half of the identity has independent rows. kronecker is Matrix.kronecker, and rankOneDensity is the frozen vecMulVec p (star p) construction."))), DescribeRole.Theorem))));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula a, Formula b) => Call("Matrix", a, b, C);
    private static Formula State(Formula n) => Mat(Fin(n), Fin(n));
    private static Formula Instance(string name, Formula type, Formula body) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp, body);
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Processor(Formula d, Formula p, Formula e) => Arrow(Mat(Product(Fin(d), Fin(p)), Product(Fin(d), Fin(p))), State(e));
    private static Formula Kron(Formula a, Formula b) => Call("kronecker", a, b);
    private static Formula Pure(Formula p) => Call("rankOneDensity", p);
    private static Formula Half => new Formula.Fraction(D(1), D(2));
    private static Formula Literal(Formula a, Formula b, Formula c, Formula d) => Seq(Bang, Bang, OpenBracket, a, Comma, Sp, b, Semi, Sp, c, Comma, Sp, d, CloseBracket);
    private static Formula AsMatrix(Formula a, Formula d) => Parenthesized(Seq(a, Sp, Colon, Sp, State(d)));
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula ChannelFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), t = F.Id("T"), r = F.Id("r"), k = F.Id("K"), i = F.Id("i"), rho = F.Id("rho");
        Formula sum = Seq(Sum, Underscore, Grp(i, Sp, Colon, Sp, Fin(r)), Sp, Parenthesized(Mul(Call("conjTranspose", At(k, i)), At(k, i))));
        Formula body = Ex("r", N, Ex("K", Arrow(Fin(r), Mat(b, a)), And(Eq(sum, D(1)),
            All("rho", Mat(a, a), Eq(At(t, rho), At(Call("ofKraus", k, k), rho))))));
        return All("A", F.Id("Type"), All("B", F.Id("Type"),
            Instance("Fintype", a, Instance("DecidableEq", a, Instance("Fintype", b, Instance("DecidableEq", b,
                All("T", Arrow(Mat(a, a), Mat(b, b)), IffOf(Call("IsChannel", t), body))))))));
    }
    private static Formula ObstructionFormula()
    {
        Formula d = F.Id("d"), p = F.Id("P"), x = F.Id("x");
        Formula input = Call("single", x, x, D(1));
        Formula Output(string name, Formula target) => Eq(At(p, Kron(input, Pure(F.Id(name)))), target);
        Formula body = Imp(And(Call("IsChannel", p), And(Output("p0", Literal(D(1), D(0), D(0), D(0))),
            And(Output("p1", Literal(D(0), D(0), D(0), D(1))), And(Output("pp", Literal(Half, Half, Half, Half)),
                Output("pm", At(Qualified("HSMul", "hSMul"), Half, AsMatrix(D(1), D(2)))))))), F.Id("False"));
        body = All("pm", Arrow(Fin(D(2)), C), body);
        body = All("pp", Arrow(Fin(D(2)), C), body);
        body = All("p1", Arrow(Fin(D(2)), C), body);
        body = All("p0", Arrow(Fin(D(2)), C), body);
        return All("d", N, All("P", Processor(d, D(2), D(2)), All("x", Fin(d), body)));
    }
}
