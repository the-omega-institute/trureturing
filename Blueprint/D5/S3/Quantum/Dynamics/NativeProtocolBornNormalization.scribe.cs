using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;
internal sealed class NativeProtocolBornNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical Born normalization for the complete original sixteen-bit protocol tree.",
        H("Complete native protocols and arbitrary position cuts"),
        Blocks(Describe.Lean(DescribeId.Create("original-complete-born-law"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization.original_complete_born_law"),
            H("The complete original tree has unit total mass and every acquired event has its actual cut trace"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/chiribella2009networks")),
            Blocks(
                Paragraph(Text("The objects are the original NativeProtocolGraft.Tree, Basis, omega0, gate, callMatrix, projector, Path and mass. Basis consists of all sixteen-bit words at the shifted original positions. The unique fixed root has ones at positions 0, 4 and 8. The proof uses the full matrices at every address in Fin 14, rather than a two-dimensional model supplied as an additional premise.")),
                Paragraph(Text("On each active center-bit pair the actual gate coefficients are a,b,c from the existing calibration calculation. Their existing squared norms, the golden quadratic identity and the actual phase norm give orthogonal unit rows. The remaining control blocks are zero or identity before the phase gate. Reindexing the full carrier by the center-bit involution proves exact energy conservation. Forward calls use this identity and inverse syntax uses nine iterations of the same actual matrix. The original resource counter still charges nine calls; no semantic equality with a separately defined matrix inverse is asserted.")),
                Paragraph(Text("The sum of all terminal squared amplitudes is conserved for every incoming full-carrier vector. Its proof recurses over the original finite tree. Each gate preserves energy, and each selector projector keeps precisely one outcome for every basis word, so the complete outcome sum preserves energy exactly. Each child can have its own feedback addresses, depth and stopping label. Unused outcomes, zero vectors, refusals, failures and early stops remain in the original Path type and its sum. No total-probability, gate-unitarity or projector-completeness certificate is an input.")),
                Paragraph(Text("Applying that conservation to the original normalized computational root gives unit total Born mass, including every final computational result. An acquired event is a Boolean function of the original prefix path, independent of any future report. The existing original_event_cut_mass_and_psd theorem supplies the same acquired event's b1 marginal and exact real trace. Its positive semidefinite matrix has nonnegative trace, giving the zero lower bound; domination by the complete Born sum gives the upper bound one. Any declared complete prefix is itself such a Tree; the theorem therefore applies at that same common cut.")),
                Paragraph(Text("For any subset I of the sixteen positions, including the empty and full subsets, splitAt is the pinned equivalence restricting a word to I and its complement. The row and complement bases are Boolean functions on those two actual position subtypes. Their dimensions are two to the cardinality of I and two to the cardinality of its complement. cutReduced is the existing right partial trace of the outer product of the same actual branch vector after this coordinate equivalence. eventCut sums those matrices over exactly the acquired histories. The existing partial-trace positivity and trace theorems supply positive semidefiniteness and equality of its complex trace with the real event mass. This reduction is a mathematical marginal and adds no physical record deletion, new register or coherent sum of distinct histories.")),
                Paragraph(Text("This is a partial consequence of V88 definitions 23.1 and 23.2 and the physical trace premise used in theorem 24.1. The same-cut integer-coordinate and signed-embedding theorem below supplies the determinant descent. The resource theorem then proves the determinant and both minimum-eigenvalue lower bounds, conditional on positive event mass and full rank of that same cut. The positive-event scalar bound reuses original_event_resource_bounds. Faithful-cut existence, the five-call reference history and the full-record Petz compiler remain separate mathematical obligations."))),
            DescribeRole.Theorem), CutNode(), CutResourceNode())));

    private static DocumentBlock CutNode() => Describe.Lean(
        DescribeId.Create("original-event-cut-integer-coordinates"),
        DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization.original_event_cut_integer_coordinates"),
        H("Quadratic integer coordinates and the exact signed embedding of the same cut"),
        StatementSource.FromAuthor(CutStatement()),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
        Blocks(
            Paragraph(Text("The theorem quantifies over the unchanged original tree, its acquired-path event and any subset I of the sixteen positions. The same eventCut supplies both the complex trace and the determinant. No positivity, covariance, gate-unitarity or normalization certificate is assumed. The statement includes zero events, singular cuts, and empty and full subsets; it makes no full-rank inference.")),
            Paragraph(Text("Let r(i) be the retained word's Hamming parity as zero or one. Let s(z) be the complementary word's parity relative to the fixed original root. Restriction along splitAt proves that the original relative exponent is r(i) plus s(z), modulo two. In the inverse-golden integer ring tau times (tau plus one) equals one. Multiplying the computed coefficient by tau plus one to the power r(i)s(z) therefore extracts the physical factors beta to r(i) and beta to s(z) without leaving the four-integer coefficient ring. The histories and the complementary word are unchanged.")),
            Paragraph(Text("cutKernel is the sum over exactly the selected original histories and complementary words of tau to s(z) times the extracted coefficient at i times the coefficient conjugate at j. This conjugation fixes the inverse-golden base ring and sends eta to minus tau minus eta. The original eventCut is the physical evaluation of this kernel multiplied on both sides by the diagonal beta to r(i). The kernel equals its coefficient conjugate transpose, so its determinant is fixed by that conjugation. In the two explicit integer coordinates this forces its eta coefficient to vanish. Multiplying its surviving inverse-golden pair by the product of tau to r(i) gives cutDetCoordinates, an actually computed element of O, with the physical determinant as its realPhysical evaluation.")),
            Paragraph(Text("conjugateEventCut applies the nonphysical homomorphism to this exact same kernel and uses the nonphysical beta on both sides. Its determinant is realConjugate of the same cutDetCoordinates. Since the nonphysical beta is imaginary, this embedded matrix equals the sum of embedded branch outer products with sign minus one to s(z) plus r(j). Equivalently it is A C A adjoint J, with complement sign C and row-parity sign J. Replacing this expression by an unsigned positive Gram matrix would change the nonphysical determinant. Coefficient conjugation is proved compatible with both S evaluations; conjugation of the square-root factor supplies the displayed sign.")),
            Paragraph(Text("These are the same-cut arithmetic descent and embedding identities used in V88 theorem 24.1, equations 24.7, 24.9 and 24.10. The resource theorem consumes them to bound the determinant and the two spectra. Positive event mass keeps its existing original_event_resource_bounds lower bound. Faithfulness means full rank of this same eventCut; positive mass alone does not imply it."))),
        DescribeRole.Theorem);

    private static DocumentBlock CutResourceNode() => Describe.Lean(
        DescribeId.Create("original-event-cut-resource-bounds"),
        DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization.original_event_cut_resource_bounds"),
        H("Sharp determinant and minimum-eigenvalue bounds at the original cut"),
        StatementSource.FromAuthor(CutResourceStatement()),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
        Blocks(
            Paragraph(Text("The objects are the same actual finite adaptive tree T, Boolean acquired-path event e and position subset I used by the preceding two theorems. Write Xi=eventCut(T,I,e), p=eventMass(T,historyEvent(e)), d=card(CutBasis(I)), L=maxCalls(T), K=kappa to the power 2Ld, and rho=Xi/p. Each inverse letter still costs nine forward calls. The trace and nonphysical bound are unconditional, including zero events and singular cuts. The scalar lower bound requires positive p, and the determinant and spectral bounds additionally require rank(Xi)=d. The two existential witnesses certify Hermiticity of Xi and of the actual normalized matrix rho; they are conclusions, not supplied certificates.")),
            Paragraph(Text("For each retained pair i,j, the exact signed embedding is summed over the unchanged original history and complementary-word pairs. Its signs have norm one. The triangle inequality and the finite Cauchy-Schwarz inequality bound the squared entry norm by the product of the two row energies. Summing over i,j gives the square of the complete original tree energy: splitAt merely reindexes every original word, and discarding the event restriction only increases that energy. Thus the embedded matrix's Frobenius norm is at most the complete tree energy, already bounded by kappa to the power 2L. No leaf count, record count or dimension multiplier enters.")),
            Paragraph(Text("For the Gram matrix M adjoint times M, all eigenvalues are nonnegative and each is at most its trace, the squared Frobenius norm of M. The product of these eigenvalues is the squared norm of det(M). This gives the determinant bound energy to the power d, hence absolute realConjugate(cutDetCoordinates) at most K for the exact embedded cut. The estimate never treats that signed matrix as positive or Hermitian.")),
            Paragraph(Text("Full rank of the physical Xi implies its matrix is a unit, so the already proved physical positive semidefiniteness gives positive definiteness and a strictly positive determinant. The existing inverse-golden integer norm lemma positive_lower applies directly to cutDetCoordinates and the proved conjugate bound. Its physical evaluation is det(Xi), so det(Xi) is at least one divided by K. This reuses the same quadratic integer coordinates and does not introduce a second norm estimate for a denominator.")),
            Paragraph(Text("The physical trace is the same raw p and is at most one. Every nonnegative eigenvalue is therefore at most one; their product, det(Xi), is at most each eigenvalue. The infimum of this finite nonempty spectrum is at least one divided by K. The existing eigenvalues_zero_smul_finite theorem identifies the actual spectrum of rho with the spectrum of Xi multiplied by one divided by that same positive p, giving the normalized lower bound one divided by Kp. Existence of a faithful original cut, the full five-call reference history, the Petz mass and full-identity complement, record extension, failure zeros and total-variation comparison, and semantic equality of the ninth power with the inverse remain separate results."))),
        DescribeRole.Theorem);

    private static Formula CutResourceStatement()
    {
        Formula L=F.Id("L"),T=F.Id("T"),e=F.Id("e"),I=F.Id("I"),h=F.Id("h"),q=F.Id("q");
        Formula cut=Call("eventCut",T,I,e),p=Call("eventMass",T,Call("historyEvent",e));
        Formula k=Power(Call("kappa"),Seq(D(2),Star,Call("maxCalls",T),Star,Call("card",Call("CutBasis",I))));
        Formula inv=Call("inv",k),rho=Call("smul",Call("complex",Call("inv",p)),cut);
        Formula ex(string name,Formula type,Formula body)=>Seq(Open,Exists,Sp,F.Id(name),Colon,Sp,type,Comma,Sp,body,Close);
        Formula imp(Formula a,Formula b)=>Seq(Open,new Formula.Logic(a,FormulaLogicOperator.Implies,b),Close);
        Formula le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
        Formula positive=new Formula.Relation(D(0),FormulaRelationOperator.LessThan,p);
        Formula spectral=ex("h",Call("IsHermitian",cut),ex("q",Call("IsHermitian",rho),
            Conj(le(inv,Call("iInf",Call("eigenvalues",h))),
                le(Seq(Frac,Grp(inv),Grp(p)),Call("iInf",Call("eigenvalues",q))))));
        Formula faithful=imp(Rel(Call("rank",cut),Eq,Call("card",Call("CutBasis",I))),
            Conj(le(inv,Call("re",Call("det",cut))),spectral));
        Formula scalar=le(Call("inv",Power(Call("kappa"),Seq(D(2),Star,Call("maxCalls",T)))),p);
        Formula law=Conj(Rel(Call("trace",cut),Eq,Call("complex",p)),
            le(Call("abs",Call("realConjugate",Call("cutDetCoordinates",T,I,e))),k),
            imp(positive,Conj(scalar,faithful)));
        return Disp(All("L",Call("Type"),All("T",Call("Tree",L),
            All("e",Call("Function",Call("Path",T),Call("Bool")),All("I",Call("Finset",Call("Fin",D(1,6))),law)))));
    }

    private static Formula CutStatement()
    {
        Formula L=F.Id("L"),T=F.Id("T"),e=F.Id("e"),I=F.Id("I"),i=F.Id("i"),j=F.Id("j"),p=F.Id("p"),z=F.Id("z");
        Formula cut=Call("eventCut",T,I,e),embedded=Call("conjugateEventCut",T,I,e);
        Formula x=Call("cutDetCoordinates",T,I,e);
        Formula wordi=Call("splitAtInverse",I,i,z),wordj=Call("splitAtInverse",I,j,z);
        Formula h=Call("branch",T,p,Call("initial"));
        Formula sign=Power(Grp(Minus,D(1)),Seq(Call("restExponent",I,z),Plus,Call("rowExponent",I,j)));
        Formula term=Seq(sign,Star,Call("conjugateAmplitude",h,wordi),Star,Call("star",Call("conjugateAmplitude",h,wordj)));
        Formula sum=FiniteSum(p,Call("Path",T),FiniteSum(z,Call("CutRest",I),
            Seq(Call("if",Call("Apply",e,p),term,D(0)))));
        Formula law=Conj(Rel(Call("trace",cut),Eq,Call("complex",Call("eventMass",T,Call("historyEvent",e)))),
            Rel(Call("det",cut),Eq,Call("complex",Call("realPhysical",x))),
            Rel(Call("det",embedded),Eq,Call("complex",Call("realConjugate",x))),
            All("i",Call("CutBasis",I),All("j",Call("CutBasis",I),Rel(Call("Apply",embedded,i,j),Eq,sum))));
        return Disp(All("L",Call("Type"),All("T",Call("Tree",L),
            All("e",Call("Function",Call("Path",T),Call("Bool")),All("I",Call("Finset",Call("Fin",D(1,6))),law)))));
    }
    private static Formula Power(Formula a,Formula b) => Seq(Grp(a),Caret,Grp(b));

    private static Formula Statement()
    {
        Formula L=F.Id("L"), T=F.Id("T"), e=F.Id("e"), I=F.Id("I"), p=F.Id("p"), z=F.Id("z");
        Formula mass=Call("eventMass",T,Call("historyEvent",e));
        Formula cut=Call("eventCut",T,I,e);
        Formula total=FiniteSum(p,Call("Path",T),FiniteSum(z,Call("Basis"),Call("mass",T,p,z)));
        Formula bounds=Conj(Rel(D(0),Leq,mass),Rel(mass,Leq,D(1)));
        Formula law=Conj(Rel(total,Eq,D(1)),bounds,Call("PosSemidef",cut),
            Rel(Call("trace",cut),Eq,Call("complex",mass)));
        return Disp(All("L",Call("Type"),All("T",Call("Tree",L),
            All("e",Call("Function",Call("Path",T),Call("Bool")),
            All("I",Call("Finset",Call("Fin",D(1,6))),law)))));
    }
    private static Formula FiniteSum(Formula i, Formula set, Formula term) =>
        Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, set), Sp, term);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula Conj(params Formula[] statements) =>
        statements.Aggregate((left, right) => Rel(left, Land, right));
}
