using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSQuotientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational boundary Gram and thirteen observable quotient coordinates",
        H("An inverse on actual raw prefix observations"), Blocks(
            Paragraph(Text("The original normalized Cramer reconstruction and its canonical core are the C8 mathematics attributed to Haobo Ma and Wenlin Zhang. This unit reuses their original minorPoly, basisNumerator, leftNumerator and matrixNumerator, together with the existing complex four-entry transfer matrix. It does not introduce a second Cramer formula, a Hermitian-coordinate transfer matrix or a new selector determinant.")),
            Definition("coreCoordinates", "Five canonical core coordinates", "Read l0, A0(0,0), A0(0,1), A1(0,0), A1(0,1) from the original reconstruction. The normalized rows l Ai=e_i and l1=1 force precisely the existing five-coordinate core shape. Original canonical_core_rigidity proves self-recovery of these coordinates."),
            Definition("boundaryLeft", "The original normalized-row contraction", "The (k,w) entry is l(w0)l(w1) if w2=k and zero otherwise. On the actual coherent chart this is a left inverse of prefixMap A l 3. The proof consumes the original boundary_contraction, after identifying the canonical shape; no extra invertibility hypothesis is imposed."),
            Definition("leftNumeratorMap", "Cleared contraction", "Replace l by the evaluated original leftNumerator b. Writing d=eval t minorPoly, the normalized contraction is d inverse squared times this matrix L0."),
            Definition("transferNumerator", "The existing four-complex-entry transfer numerator", "Let N_i be the original matrixNumerator evaluation. M is transferMatrix N, exactly the evaluation of numeratorTransfer in independent t and conjugate-t variables. The canonical transfer matrix is h(d)/h(v) times M, where v=eval t basisNumerator.det and h(z)=z conjugate(z)."),
            Definition("modulus", "Algebraic squared modulus", "The complex scalar z conjugate(z), equal on actual complex values to the real norm square embedded into the complex numbers."),
            Definition("gramNumerator", "Exact cleared boundary numerator", "For Q=Q3, t is its fixed all-zero column and B=L0 Q L0 dagger. The numerator is h(v)^m times unvec(adj(M)^m vec(B)). The exponent m is the actual complement length. The transfer inverse need not preserve positivity on arbitrary input matrices."),
            Definition("gramDenominator", "Exact scalar denominator", "The denominator is h(d)^(m+2) det(M)^m. The extra square comes from the two normalized-row boundary contractions. There is no determinant of a new selector, and det(M) is not det(A0+A1)."),
            Definition("boundaryGram", "Rational observable boundary Gram", "Divide the displayed numerator by the displayed denominator. This is defined on arbitrary observed matrices; the theorem identifies it with the actual full-length canonical boundary Gram only on actual free-boundary MPS in the fixed recovery chart."),
            Theorem("actual_boundary_gram", "The full-length actual boundary Gram", ActualGram(), "The observed coherent vector is produced from the actual density by observed_coherent. The original gauge_lift supplies the full-length canonical boundary q. Apply density_factor, contract on both sides with the original normalized-row left inverse, flatten the four complex entries, and iterate transferMatrix_apply. The adjugate identity and exact scalar cancellation recover q q dagger. The inverse transfer is algebraic; positivity is obtained from this actual rank-one Gram identity, rather than asserted for the inverse on arbitrary matrices."),
            Definition("polynomialConjugate", "Conjugation of paired polynomial variables", "Conjugate every coefficient and swap the original and conjugate variable labels. This is the generic original conjugation operation used by both the observable quotient and native independent-trial interior polynomial recurrences."),
            Describe.Lean(DescribeId.Create("quotient-polynomial-conjugate-eval"),
                DeclarationHandle.Create(Module + ".polynomialConjugate_eval"), H("Exact conjugate-diagonal evaluation"),
                StatementSource.FromAuthor(Disp(ConjugateFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every index type, polynomial and complex variable assignment, actual evaluation of polynomialConjugate is the conjugate of actual evaluation. Coefficient conjugation and the variable swap both contribute; coefficient conjugation alone would not conjugate the paired variables. The original proof is reused unchanged by the native interior polynomial adjoints."))), DescribeRole.Theorem),
            Definition("boundaryGramPolynomial", "A literal polynomial numerator", "The variables are all entries of Q and independent conjugate entries, not merely points in a parametrized image. Substitute the selected column into the original Cramer polynomials, conjugate by coefficient conjugation and swapping the paired variables, form L0 Q L0 dagger, and apply the original transfer adjugate power. The exact evaluation is gramNumerator for every complex matrix Q."),
            Definition("boundaryDenominatorPolynomial", "A literal polynomial denominator", "In the same paired observed variables, form h(d)^(m+2) det(M)^m. Its evaluation is exactly gramDenominator on every observed matrix."),
            Definition("quotientCoordinates", "The rational phase quotient", "The coordinates are five complex canonical core entries, sigma=Re G00 and eta=G10/G00, thirteen real numbers in total. On actual points with G00 nonzero, sigma=normSq(q0)>0 and eta=q1/q0. The lower-left orientation is essential."),
            Definition("positiveBoundary", "A positive phase representative", "The representative boundary is (sqrt(sigma), sqrt(sigma) eta). This realization uses a square root. It is not called rational and is separate from the rational coordinate inverse and polynomial raw observations."),
            Theorem("actual_quotient_representative", "Exact unit-phase reconstruction", Representative(), "First recover the actual boundary Gram. Nonzero G00 then implies q0 nonzero, sigma strictly positive, and the correctly oriented ratio eta=q1/q0. The constructed positive boundary has exactly the same Gram, and the original boundary_phase theorem gives an exact unit complex phase between the full states. Raw affine scale is retained."),
            Definition("quotientObservation", "Polynomial raw observations on the quotient", "For any prefix length k and complement length m use boundary (1,eta), the original canonical core and left row, then multiply the entire raw density by the real sigma. No square root occurs in this observation map."),
            Theorem("quotient_retraction", "Exact thirteen-coordinate observable retraction", Retraction(), "For sigma>0 the observation is the actual raw density of the positive-boundary representative. Original canonical-core rigidity and the actual boundary Gram return the same core, sigma and eta. No coherent sum-tail, invertibility of A0+A1, two-site leading block or genericity condition is added to the original fixed-density recovery condition."),
            Definition("quotientLocusPolynomial", "An explicit refined observed chart", "Multiply the existing real observed recovery polynomial by the norm-square polynomial of the boundary numerator at 00. Its nonvanishing is exactly recovery plus a nonzero numerator at 00. It is a literal real polynomial on the arbitrary-entry observed matrix space."),
            Theorem("quotient_locus_witness", "A nonzero actual witness at every length", Witness(), "Use the original matrices [[1,2],[3,4]] and [[5,6],[7,8]], left (1,0), right (1,2), for every N=3+m. The original fixed-density positivity and recovery witness supply the recovery condition. The original full-length witness_gauge identifies the canonical boundary, whose first coordinate is 5 times 2^(2+m), hence nonzero. The exact recovered Gram gives a nonzero 00 numerator without presupposing membership in the refined chart. This is an actual-image witness, with no replacement by a Zariski closure."),
            Definition("positiveGramPolynomial", "The positive-denominator numerator", "Multiply boundaryGramPolynomial by conjugate(det(M))^m. This is still a literal paired-variable polynomial."),
            Definition("positiveGramDenominator", "A positive real denominator", "The denominator is normSq(d)^(m+2) normSq(det(M))^m. It is strictly positive on the original observed recovery chart. The exact corresponding numerator is the positiveGramPolynomial evaluation."),
            Definition("quotientRealCoordinates", "The thirteen real coordinates", "The index is Fin 5 plus Fin 5 plus Fin 3: five real core parts, five imaginary core parts, sigma, real eta, imaginary eta."),
            Definition("quotientRealNumerator", "Real polynomial coordinate numerators", "Each complex quotient p/q is multiplied by conjugate(q). Convert the paired-variable polynomial to Cartesian variables using the existing coordinate equivalence, then take coefficientwise real or imaginary parts. These are additive coefficient maps, not ring homomorphisms."),
            Definition("quotientRealDenominator", "Real polynomial coordinate denominators", "Use the existing sum-of-squares normPolynomial of q. Every denominator is strictly positive on the refined chart. The construction gives actual ratios of real polynomials, not a smoothness or analyticity substitute."),
            Definition("quotientObservationPolynomial", "Real polynomial raw observation entries", "Substitute the canonical core and boundary (1,eta) into the original twelve-complex-parameter amplitude polynomials. Multiply the amplitude/conjugate-amplitude complement sum by sigma, then take coefficientwise real or imaginary parts. The universal evaluation identity holds for every real quotient parameter, every prefix and complement length, and either component; no square root or positivity condition is used in this polynomial identity."),
            Theorem("rational_quotient_inverse", "Rationality with exact real polynomial expressions", Rational(), "There are exactly thirteen real indices. For every index the named real polynomial denominator is positive on the refined observed chart and the ratio of the named real polynomial numerator and denominator is exactly the corresponding quotient coordinate. The theorem also gives the full Gram with its positive real denominator and exact polynomial numerator, the universal polynomial evaluation identity for every raw quotient observation entry, and the nonzero 00 Gram entry required by the actual-state representative theorem. The statement holds on arbitrary observed matrices satisfying this explicit polynomial condition; its interpretation as a rank-one physical boundary Gram additionally uses actual_boundary_gram."),
            Paragraph(Text("The interior-genericity consumer uses canonical_shape in place, with its original telescope and proof, to align the actual quotient core with canonicalCore before transferring injectivity. Its public helper audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/30422. This is a rational inverse unit for the prefix N=3+m, including every original N at least four. It does not prove generic-point Q2 ambiguity on a dense intrinsic actual-image locus, compose the later maximal-rank and C1 fiber argument, or settle Conjecture 9. No solved-open-problem increment, interior-window theorem, normalized-state statement, dynamics, time group, energy, physical clock, physical recovery operation, stability, sample complexity or thermodynamic cost is asserted.")))));

    private static DocumentBlock Definition(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("quotient-" + name.ToLowerInvariant()), DeclarationHandle.Create(Module + "." + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Module + "." + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula ActualGram() {
        var m=X("m"); var p=X("psi"); var q=X("q"); var Q=Raw(m,p); var t=At("fixedTensor",Q);
        var full=At("mpsState",N(m),At("canonicalCore",t,D(0)),At("canonicalCore",t,D(1)),
            At("reconstructedLeft",t),q);
        var gram=Eq(At("boundaryGram",m,Q),At("vecMulVec",q,At("star",q)));
        var result=Some("q",Arrow(At("Fin",D(2)),Complex),And(Eq(p,full),gram));
        return All("m",Nat,All("psi",State(m),
            Imp(And(Member(p,At("openBoundaryMPS",N(m))),Recovery(Q)),result)));
    }
    private static Formula Representative() {
        var m=X("m"); var p=X("psi"); var Q=Raw(m,p); var c=At("quotientCoordinates",m,Q); var z=X("z");
        var full=At("mpsState",N(m),At("core",c,D(0)),At("core",c,D(1)),At("left",c),
            At("positiveBoundary",c));
        var phase=Some("z",Complex,And(Eq(At("norm",z),D(1)),Eq(p,At("smul",z,full))));
        var conditions=And(Member(p,At("openBoundaryMPS",N(m))),Recovery(Q),
            Ne(At("boundaryGram",m,Q,D(0),D(0)),D(0)));
        return All("m",Nat,All("psi",State(m),Imp(conditions,And(Lt(D(0),At("sigma",c)),phase))));
    }
    private static Formula Retraction() {
        var m=X("m"); var p=X("p"); var Q=At("quotientObservation",D(3),m,p);
        return All("m",Nat,All("p",At("Quotient"),Imp(And(Lt(D(0),At("sigma",p)),Recovery(Q)),Eq(At("quotientCoordinates",m,Q),p))));
    }
    private static Formula Witness() {
        var m=X("m"); var p=At("mpsState",N(m),At("originalCore",D(0)),At("originalCore",D(1)),At("vector",D(1),D(0)),At("vector",D(1),D(2)));
        return All("m",Nat,And(Member(p,At("openBoundaryMPS",N(m))),Locus(m,Raw(m,p)),Recovery(Raw(m,p)),Ne(At("boundaryGram",m,Raw(m,p),D(0),D(0)),D(0))));
    }
    private static Formula Rational() {
        var m=X("m"); var Q=X("Q"); var i=X("i"); var j=X("j"); var coords=At("realCoordinates",At("entries",Q));
        var den=At("MvPolynomial.eval",coords,At("quotientRealDenominator",m,i));
        var num=At("MvPolynomial.eval",coords,At("quotientRealNumerator",m,i));
        var real=All("i",At("QuotientRealIndex"),And(Lt(D(0),den),Eq(new Formula.Fraction(num,den),At("quotientRealCoordinates",At("quotientCoordinates",m,Q),i))));
        var pd=At("positiveGramDenominator",m,Q);
        var gram=All("i",At("Fin",D(2)),All("j",At("Fin",D(2)),Eq(At("boundaryGram",m,Q,i,j),new Formula.Fraction(At("PhasePolynomial.actual",At("positiveGramPolynomial",m,i,j),At("entries",Q)),At("Complex.ofReal",pd)))));
        var k=X("k"); var a=X("a"); var u=X("u"); var v=X("v"); var flag=X("imaginary"); var p=X("p");
        var poly=All("k",Nat,All("a",Nat,All("u",At("Word",k),All("v",At("Word",k),All("imaginary",At("Bool"),All("p",At("Quotient"),Eq(At("MvPolynomial.eval",At("quotientRealCoordinates",p),At("quotientObservationPolynomial",k,a,u,v,flag)),At("component",flag,At("quotientObservation",k,a,p,u,v)))))))));
        return All("m",Nat,All("Q",At("Matrix",At("Word",D(3)),At("Word",D(3)),Complex),Imp(Locus(m,Q),And(Eq(At("Fintype.card",At("QuotientRealIndex")),D(1,3)),real,Lt(D(0),pd),gram,poly,Ne(At("boundaryGram",m,Q,D(0),D(0)),D(0))))));
    }
    private static Formula Raw(Formula m, Formula p)=>At("rawPrefix",D(3),m,p);
    private static Formula Recovery(Formula Q)=>Ne(At("MvPolynomial.eval",At("realCoordinates",At("fixedTensor",Q)),At("recoveryPolynomial")),D(0));
    private static Formula Locus(Formula m,Formula Q)=>Ne(At("MvPolynomial.eval",At("realCoordinates",At("entries",Q)),At("quotientLocusPolynomial",m)),D(0));
    private static Formula N(Formula m)=>new Formula.Binary(D(3),FormulaBinaryOperator.Add,m);
    private static Formula State(Formula m)=>Arrow(At("Word",N(m)),Complex);
    private static Formula X(string name)=>F.Id(name);
    private static Formula Complex=>Seq(Mathbb,Grp(X("C")));
    private static Formula Nat=>Seq(Mathbb,Grp(X("N")));
    private static Formula At(string name,params Formula[] args) {
        var items=new List<Formula>();
        foreach (var part in name.Split('.')) {
            if (items.Count>0) items.Add(Dot);
            items.Add(X(part));
        }
        return new Formula.Apply(Seq(Operatorname,Grp(Seq([..items]))),[..args]);
    }
    private static Formula Par(Formula a)=>Seq(Open,a,Close);
    private static Formula All(string x,Formula type,Formula body)=>Seq(Forall,Sp,Par(Seq(X(x),Colon,Sp,type)),Comma,Sp,Par(body));
    private static Formula Some(string x,Formula type,Formula body)=>Seq(Exists,Sp,Par(Seq(X(x),Colon,Sp,type)),Comma,Sp,Par(body));
    private static Formula Arrow(Formula a,Formula b)=>new Formula.TypeArrow(a,b);
    private static Formula Imp(Formula a,Formula b)=>Arrow(Par(a),Par(b));
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Member(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula And(params Formula[] fs)=>fs.Aggregate((a,b)=>new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b)));

    private static Formula ConjugateFormula() => All("K",X("Type"),All("p",At("PhasePolynomial",X("K")),All("z",At("Function",X("K"),X("Complex")),
        Eq(At("actual",At("polynomialConjugate",X("p")),X("z")),At("star",At("actual",X("p"),X("z")))))));
}
