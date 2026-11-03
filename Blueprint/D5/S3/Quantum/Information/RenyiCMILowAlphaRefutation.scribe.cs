using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class RenyiCMILowAlphaRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/RenyiCMILowAlphaRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/seshadreesan2015renyi");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact faithful state and a rectangular Kraus channel contradict the original optimized SBW A-channel inequality at alpha = 1/2.",
        H("The original low-alpha SBW assertion"),
        Blocks(
            Describe.Lean(DescribeId.Create("sbw-low-alpha-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The assertion on 0 < alpha < 1"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The claim quantifies over every natural input and output dimension and finite Kraus count. A positive semidefinite trace-one input and a complete Kraus family acting only on A must satisfy renyiCMI(alpha,applyA(K,rho)) <= renyiCMI(alpha,rho) for every 0 < alpha < 1. The functional, continuous-functional-calculus powers, Kraus action and carrier ((A times B) times E) are imported unchanged from RenyiCMILocalChannelRefutation. At alpha=1/2, the counterexample below makes the output functional strictly larger than the input functional. The frozen expression is the original optimized quantity; no fixed-sigma, sandwiched replacement or log-Euclidean quantity is substituted."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sbw-low-alpha-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A half-alpha counterexample"), StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Set t=2^(-30), with input dimensions (3,2,2) and output dimensions (2,2,2). Let H have rows (0,1) and (1,0), R0=diag(16,1)/68, R1=diag(1,16)/68 and R2=identity/4. The state is block diagonal in A and B, with E blocks (Ra+(-1)^b*t*Xa)/2, where X0=X1=H and X2=-6H. All six blocks are positive definite by their positive first diagonal entry and determinant, and the total trace is one.")),
                    Paragraph(Text("The three rectangular Kraus matrices map input basis label j to output label 0 for j=0,1 and to output label 1 for j=2, and vanish on the other labels. Their adjoint products sum to identity. The actual frozen applyA sum gives output E blocks (identity/4+2*(-1)^b*t*H)/2 and (identity/4-6*(-1)^b*t*H)/2. The input AE marginal is the block sum of R0,R1,R2, the output AE marginal is identity/4 and both E marginals are identity/2.")),
                    Paragraph(Text("For a positive two by two real symmetric block M with entries (a,u;u,b), d=sqrt(a*b-u^2) and g=sqrt(a+b+2*d), its positive square root is (M+d*identity)/g. The proof checks this square and positivity, then identifies it with the frozen CFC half power by square-root uniqueness. Positive fourth-root certificates similarly identify the AE quarter powers; an inverse certificate identifies the E negative quarter power. Thus the original order of the two quarter powers and the partial trace is retained.")),
                    Paragraph(Text("Write x=t^2, r=sqrt(1-289*x), s=sqrt(17+8*r), p=sqrt(1-64*x), q=sqrt(1-576*x), m=sqrt((1+p)/2), n=sqrt((1+q)/2), a=5*(s^2+9)/(34*s) and b=4/s. Exact evaluation of the frozen half-alpha expression gives the input value -log(Zin) and output value -log(Zout), with Zin=(a+n)^2/4+4*x*(b-3/n)^2 and Zout=(m+n)^2/4+4*x*(1/m-3/n)^2. The matrix identities preceding these real expressions evaluate actual states and Kraus output, rather than assuming scalar values for them.")),
                    Paragraph(Text("The exact comparison factors as Zout-Zin=(m-a)*(m+a+2*n)/4+4*x*(1/m-b)*(1/m+b-6/n). On 0<x<=10^(-8), the radical relations give 1-a<(5441/500)*x and 1-m>=8*x. The first summand is therefore less than (1441/500)*x. They also give 1/m-b>=1999/10000 and 1/m+b-6/n<=-41989/10000. The second summand is at most -4*(1999/10000)*(41989/10000)*x. Their sum is strictly less than -(473/1000)*x. The fixed x=2^(-60) lies in that interval. Positivity of Zout and strict monotonicity of the natural logarithm give output CMI strictly greater than input CMI, contradicting claim at alpha=1/2.")),
                    Paragraph(Text("The counterexample refutes the low-alpha mathematical assertion for the original optimized functional. The alpha=2 theorem remains a separate result. The recent log-Euclidean and dual-J counterexamples concern different functionals and are not used as evidence for this theorem. No worldwide novelty or priority claim is made."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name)
    {
        string[] words = name.Split('.');
        Formula[] items = new Formula[words.Length * 2 - 1];
        for (int i = 0; i < words.Length; i++)
        {
            items[2 * i] = F.Id(words[i]);
            if (i + 1 < words.Length) items[2 * i + 1] = Dot;
        }
        return Seq(Operatorname, Grp(items));
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Product(Formula a, Formula b) => Par(Seq(a, Sp, Times, Sp, b));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static Formula ClaimFormula()
    {
        Formula alpha = F.Id("alpha"), rho = F.Id("rho"), k = F.Id("K");
        Formula a = Call("Fin", F.Id("dA")), ap = Call("Fin", F.Id("dAPrime")),
            b = Call("Fin", F.Id("dB")), e = Call("Fin", F.Id("dE"));
        Formula index = Product(Product(a, b), e);
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", index, index, complex);
        Formula kraus = new Formula.TypeArrow(Call("Fin", F.Id("r")), Call("Matrix", ap, a, complex));
        Formula complete = Eq(Seq(Sum, Underscore, Grp(F.Id("j")), Sp,
            new Formula.Binary(Call("conjTranspose", Call("K", F.Id("j"))), FormulaBinaryOperator.Multiply, Call("K", F.Id("j")))), D(1));
        Formula range = new Formula.Logic(Par(Less(D(0), alpha)), FormulaLogicOperator.And, Par(Less(alpha, D(1))));
        Formula inequality = new Formula.Relation(Call("renyiCMI", alpha, Call("applyA", k, rho)),
            FormulaRelationOperator.LessThanOrEqual, Call("renyiCMI", alpha, rho));
        Formula body = Imp(Call("Matrix.PosSemidef", rho), Imp(Eq(Call("Matrix.trace", rho), D(1)), Imp(complete, Imp(range, inequality))));
        Formula quantified = All("dA", Naturals, All("dAPrime", Naturals, All("dB", Naturals, All("dE", Naturals,
            All("r", Naturals, All("rho", matrix, All("K", kraus, All("alpha", Reals, body))))))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Par(quantified)));
    }
}
