using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class UniformSignatureCodeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed alphabet encodes the truncated ancestor signature at every depth of the ordered address tree.",
        H("Uniform Static Signature Code"), Blocks(
            Def("alphabetSize", "The alphabet size",
                "Write N(0)=1 and N(h+1)=3 times 2 to the power h. The size depends only on the natural signature budget, independently of the address depth and its current colour."),
            Def("Alphabet", "Backward increment choices",
                "The zero-budget alphabet is Unit. At positive budget h+1 it is Fin 3 times the Boolean functions on Fin h. The three-valued coordinate records the incoming increment, ordered minus, zero, plus. For a child increment zero, the possible parent increments are minus and plus; for plus they are zero and plus; for minus they are minus and zero. False selects the smaller parent increment and true the larger. These are the backward rows of the fixed ordered child-increment table."),
            Def("encode", "A symbol for every finite address",
                "At budget h+1, record the current incoming increment and h bits. Bit j records the backward choice from ancestor j to ancestor j+1 when j+1 is strictly smaller than the depth. Otherwise the bit is false. Thus the root uses a fixed symbol and short addresses pad every unused bit with false. No root incoming increment is requested as a backward choice. At budget zero use the unique Unit symbol."),
            Describe.Lean(DescribeId.Create("uniform-static-signature-code"),
                DeclarationHandle.Create(Prefix + "uniform_signature_code"),
                H("One alphabet decodes all depths"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural modulus m at least three and every natural budget h, there exist a single map alpha from all finite literal addresses to Fin N(h) and a total function D from (ZMod m times Nat) times Fin N(h) to Nat times List (ZMod m), such that D(observation(m,p),alpha(p)) equals signature(m,h,p) for every address p. Both maps are chosen before the address is quantified. The observation supplies exactly the current colour and its unbounded natural depth.")),
                    Paragraph(Text("The concrete symbol is encode transported along a finite equivalence to Fin N(h). Equal symbols give the same initial increment. At each further nonroot ancestor the corresponding equal bits and the backward table recover the same parent increment. Induction recovers all increments needed through min(h,depth). The incoming-colour identity then gives the next colour by subtracting that increment from the current colour. Induction therefore gives the entire original signature, including depth and the current colour.")),
                    Paragraph(Text("The zero-budget signature follows from the observation alone. At every budget the root signature contains just its initial colour; at short addresses the colour list stops at the root. The proof covers arbitrarily large finite depths. Constancy of the signature on each combined observation-and-symbol fibre gives a total decoder by AnswerabilityCriterion.answerability_criterion; values on inputs outside the represented range are unrestricted.")),
                    Paragraph(Text("This is the upper construction in finite joint cycle and radial prediction, Definition 3.1 and Theorem 3.2, with the ordered recursion of Continuation V, Definition 120.3. It is a static deterministic representation of the signature. It gives no lower bound or optimality assertion, and no procedure for acquiring a symbol, online workspace bound, sample bound, storage guarantee, or additional stochastic-law statement."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("uniform-signature-code-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula ResultFormula()
    {
        Formula m = V("m"), h = V("h"), p = V("p");
        Formula nat = Call("Nat"), address = Call("Address"), colour = Call("ZMod", m);
        Formula alphabet = Call("Fin", Call("alphabetSize", h));
        Formula observation = Par(Seq(colour, Sp, Times, Sp, nat));
        Formula domain = Par(Seq(observation, Sp, Times, Sp, alphabet));
        Formula target = Par(Seq(nat, Sp, Times, Sp, Call("List", colour)));
        Formula equation = Seq(Call("D", Par(Seq(Call("observation", m, p), Comma, Sp,
            Call("alpha", p)))), Sp, Eq, Sp, Call("signature", m, h, p));
        return Disp(All("m", nat, Seq(Par(Seq(D(3), Sp, Le, Sp, m)), Sp, Implies, Sp,
            Par(All("h", nat, Ex("alpha", Seq(address, Sp, To, Sp, alphabet),
                Ex("D", Seq(domain, Sp, To, Sp, target), All("p", address, equation))))))));
    }
}
