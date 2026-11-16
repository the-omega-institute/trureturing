using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSInteriorTransversalityCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Division-free integer recurrences certify nonzero real derivative slopes at every pair of positive exterior lengths.",
        H("The all-length integer transversality certificate"), Blocks(
            Definition("lu", "The left covector recurrence", "The integer triple lu starts at (1,0,-1) and sends (a,b,c) to (3a-2b,5c,-2a+3b). Its real cast computes the left inverse-power readout in OpenBoundaryMPSInteriorTransversality.left_inverse_read."),
            Definition("lv", "The left target recurrence", "The integer triple lv starts at (1,0,1) and sends (a,b,c) to (3a+2b,c,2a+3b). Its real cast computes the actual left target in OpenBoundaryMPSInteriorTransversality.left_forward_coords."),
            Definition("rx", "The right inverse-power recurrence", "The integer triple rx starts at (0,1,0) and sends (a,b,c) to (3a-2b,5c,-2a+3b). Its real cast computes the radial inverse-power contribution in the consuming transversality proof."),
            Definition("ry", "The right target recurrence", "The integer triple ry starts at (1,0,0) and sends (a,b,c) to (3a+2c,2a+3c,b). Its real cast computes the iterated actual right environment in the consuming transversality proof."),
            Definition("U", "The left slope numerator", "U(0)=0 and U(n+1)=5U(n)+2(lu(n+1,0)lv(n+1,1)+lu(n+1,1)lv(n+1,0)). The consuming proof establishes U(p)=5^p L after casting to the reals."),
            Definition("V", "The right slope numerator", "V(0)=0 and V(n+1)=5V(n)+2(-1)^(n+2)(rx(n+1,0)+5^(n+1)ry(n+2,2)). The consuming proof establishes V(q)=5^q R after casting to the reals."),
            Describe.Lean(DescribeId.Create("interior-transversality-certificate-nonzero"),
                DeclarationHandle.Create(Module + ".certificate_nonzero"),
                H("Nonzero integer slope certificates at all positive lengths"),
                StatementSource.FromAuthor(Disp(Certificate())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For positive p and q, both integer numerators are nonzero and their product has the displayed residue in ZMod 5. Induction on the vector recurrences gives lu(n+1)=3^(n+1)(1,0,1), lv(n+1)=2^n(3,1,2), and rx(n+1)=3^(n+1)(1,0,1) modulo 5. Substitution in the scalar recurrences yields U(p)=1 and V(q)=2(-1)^(q+1)3^q modulo 5. Since the latter residue is nonzero, neither integer numerator vanishes.")),
                    Paragraph(Text("OpenBoundaryMPSInteriorTransversality consumes the recurrences in its coordinate and finite-sum inductions, then consumes certificate_nonzero to construct the invertible ordinary real derivative at the fixed native sector and boundaries. This is an integer certificate for that witness; full C9 remains open and the solved-open-problem count remains zero. It supplies no physical positive inverse, normalization, dynamics, time, energy or thermodynamic conclusion."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("interior-transversality-certificate-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Certificate()
    {
        var p = Id("p"); var q = Id("q");
        return All("p", Id("Nat"), All("q", Id("Nat"),
            Imp(And(Le(D(1),p),Le(D(1),q)),
                And(Ne(Call("U",p),D(0)),Ne(Call("V",q),D(0)),
                    Eq(Call("intCastZModFive",Mul(Call("U",p),Call("V",q))),
                        Mul(Mul(D(2),Pow(new Formula.Negate(D(1)),Add(q,D(1)))),Pow(D(3),q)))))));
    }
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s),[..xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s),t,b);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b) => new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a, Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a),b);
}
