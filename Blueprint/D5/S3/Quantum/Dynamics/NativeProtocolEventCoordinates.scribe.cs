using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;
internal sealed class NativeProtocolEventCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native event coordinates and whole-tree conjugate energy",
        H("Native event coordinates and whole-tree conjugate energy"),
        Blocks(CoordinateNode())));

    private static DocumentBlock CoordinateNode() => Describe.Lean(
        DescribeId.Create("original-event-coordinates-and-bound"),
        DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolEventCoordinates.original_event_coordinates_and_bound"),
        H("Computed integer coordinates and the whole-tree signed conjugate bound"),
        StatementSource.FromAuthor(CoordinateStatement()),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
        Blocks(
            Paragraph(Text("For every terminal-label type L, original native tree T and Boolean terminal event e, coordinates(T,e) is an explicitly computed integer pair A,B in the inverse-golden basis. The physical evaluation is A+B t, with t=phi inverse; its other real evaluation is A-B phi. The displayed theorem identifies the first value with the actually computed raw eventMass, identifies the second value with a signed sum over the same terminal paths and basis words, and bounds its absolute value using L(T)=Tree.maxCalls(T) and kappa=1+2 phi cubed.")),
            Paragraph(Text("The coefficient ring O consists of integer pairs with generator tau satisfying tau squared equals one minus tau. S consists of two O coordinates with generator eta satisfying eta squared equals minus one minus tau eta. These are Mathlib quadratic algebras; their multiplication and both evaluation homomorphisms are proved from the displayed equations. At each full basis word z the coefficient vector h represents the actual amplitude as beta to exponent(z) times physical(h(z)). The exponent is zero or one according to the Hamming parity relative to the actual root at shifted positions 0,4,8. A center-bit flip changes that parity.")),
            Paragraph(Text("The forward update is diagStep(j,z) h(z) plus offStep(j,z) tau to (one minus exponent(z)) h(flip(j,z)). Here diagStep is eta times one plus (eta minus one) times the actual diagonal of P; offStep is tau eta (eta minus one) on the 00 neighboring-control block and zero elsewhere. The proof expands the original number projections and bit flip on all sixteen-bit words and all fourteen addresses. Branch transport follows the original chronological operator product, with nine updates for inverse syntax. A report multiplies each coefficient by its original selector indicator, and all report outcomes remain in the tree.")),
            Paragraph(Text("For H=a+b eta, its quadratic norm in S is a squared minus tau a b plus b squared. The event coordinates sum tau to exponent(z) times this norm only on the selected original terminal coordinates. Under the physical evaluation this is exactly the original squared amplitude. Under tau mapped to minus phi, eta mapped to exp(pi i/5), and beta mapped to i sqrt(phi), it equals minus one to exponent(z) times the embedded squared amplitude. This sign is essential: the second evaluation is not a positive Born mass. No field-membership certificate or assumed event law is present.")),
            Paragraph(Text("The embedded active block has squared operator bound phi to the sixth, obtained by two-coordinate Cauchy-Schwarz and reindexing by the same center-bit involution. The remaining control blocks are zero or identity. The gate norm is therefore at most kappa. Induction on the complete tree sums all measurement energies before comparing the child maxima with the original maximum; selector completeness gives exact energy conservation even for non-surjective selectors. This proves a whole-tree bound with no leaf, report or branch-count factor. Zero-mass deep branches and nine-cost calls retain their syntactic resource cost.")),
            Paragraph(Text("The cut-determinant construction is a pending extension of the existing coefficient representation. Its complete original-cut correspondence remains unverified; the existing event theorem does not establish this route. The formulas below specify the required correspondence and do not add a theorem or coverage claim.")),
            Paragraph(Text("For the original cut-determinant application, fix any subset I of the sixteen positions, and split a basis word into its restrictions r on I and z on its complement. This includes the empty and full subsets. For every actual tree T and acquired-history event e, Xi(r,s) is the sum over selected histories h and the same complementary word z of c_h(r,z) times the physical conjugate of c_h(s,z). Each c_h is the existing actual branch product on the fixed root; branch_physical supplies its coefficient representation beta to exponent(r,z) times physical(F_h(r,z)), with F_h computed by branch(T,h,initial). No arbitrary matrix or assumed quadratic-membership certificate is used.")),
            Paragraph(Text("Work in the free integral coefficient algebra K=S[B]/(B squared minus tau), over the existing S and O=Z[tau]. This is a coordinate algebra, not a constructed degree-eight field. The beta-sign involution fixes S and sends B to minus B. Physical conjugation instead fixes B and conjugates both S coefficients using eta sent to minus tau minus eta. These two explicitly defined maps commute. Evaluation sends B to the original beta and uses the same existing t and zeta on S; beta squared equals t verifies the homomorphism law. Applying it to each computed branch coefficient gives the original c_h, so entrywise evaluation of the coefficient cut matrix gives the original Xi exactly.")),
            Paragraph(Text("The Hamming parity of the full word splits into its I parity and complementary parity relative to the same fixed root. In a reduced entry, the complementary word occurs twice. Therefore the beta-sign map sends the coefficient cut matrix to J Xi_K J, where J is the diagonal row-parity sign matrix and J squared is identity. The distinct physical conjugation sends Xi_K to its transpose. The pinned RingHom.map_det, Matrix.det_mul and Matrix.det_transpose identities then make its determinant fixed under both maps. In the two nested quadratic coordinates, the first invariance forces the B coefficient to vanish; the second forces the remaining cyclotomic imaginary coefficient to vanish. The surviving coordinate x=A+B_0 tau is computed from that same determinant, with A and B_0 integers.")),
            Paragraph(Text("Once the two fixed-coordinate identities and actual evaluation correspondence are verified, the physical determinant D equals A+B_0 t and is integral over the integers, using the existing t_integral. This would apply the existing branch representation and pinned algebra identities, with no additional D5 binding declaration. Reuse norm_product and norm_zero in Coeff for x: the product of D and its other real evaluation A minus B_0 phi equals the integer norm A squared minus A B_0 minus B_0 squared. If D is nonzero this norm is nonzero, and int_abs_lower gives one less than or equal to the absolute value of D times that same other evaluation. The intended domain is every original position subset and acquired-history event, including zero events; it exceeds the existing b1 calibration result.")),
            Paragraph(Text("This descent does not bound the other determinant evaluation by kappa to twice Ld. That actual same-tree estimate, its extension/restriction correspondence with the nonphysical branch coefficients, the determinant resource lower bound and both minimum-eigenvalue bounds remain separate obligations of source theorem 24.1. The physical complete-tree normalization and arbitrary-position cut trace are supplied separately by NativeProtocolBornNormalization; the faithful conditional calibration still requires its original consumers. No claim that arbitrary embeddings commute with physical conjugation is used.")),
            Paragraph(Text("This event theorem does not identify an original cut reduction or prove its determinant or spectral lower bounds. It does not construct the actual chi state, Petz comparison, full record-law bridge or Born normalization, and it does not prove that the ninth gate power is the semantic inverse."))),
        DescribeRole.Theorem);

    private static Formula CoordinateStatement()
    {
        Formula L=F.Id("L"), T=F.Id("T"), e=F.Id("e"), p=F.Id("p"), z=F.Id("z");
        Formula x=Call("coordinates",T,e), nu=Call("realConjugate",x);
        Formula signed=Seq(Power(Grp(Minus,D(1)),Call("exponent",z)),Star,
            Call("normSq",Call("conjugateAmplitude",Call("branch",T,p,Call("initial")),z)));
        Formula sum=FiniteSum(p,Call("Path",T),FiniteSum(z,Call("Basis"),
            IfThenElse(Call("Apply",e,p,z),signed,D(0))));
        Formula K=Power(Call("kappa"),Seq(D(2),Star,Call("maxCalls",T)));
        return Disp(All("L",Call("Type"),All("T",Call("Tree",L),All("e",Call("Events",T),
            And(Rel(Call("eventMass",T,e),Eq,Call("realPhysical",x)),
                Rel(nu,Eq,sum),Leq(Call("abs",nu),K))))));
    }

    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);

    private static Formula Power(Formula a, Formula b) => Seq(Grp(Parenthesized(a)), Caret, Grp(b));

    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, condition, Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);

    private static Formula Rel(Formula a, Formula op, Formula b) =>
        Seq(Open, a, Sp, op, Sp, b, Close);

    private static Formula And(params Formula[] xs) =>
        xs.Aggregate((a,b) => Rel(a,Land,b));

    private static Formula FiniteSum(Formula i, Formula set, Formula term) =>
        Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, set), Sp, term);
}
