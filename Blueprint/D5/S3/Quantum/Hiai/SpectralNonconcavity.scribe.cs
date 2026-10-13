using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class SpectralNonconcavityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Hiai/SpectralNonconcavity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/hiai2025spectralnonconcavity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The UNTILDE spectral trace has a strict affine Jensen violation at every off-midpoint parameter, already among real symmetric faithful qubit density matrices.",
        H("Off-midpoint obstruction for the original spectral mean"), Blocks(
            Paragraph(Text("SpectralNonconcavityScalars owns the pure real ordered-root algebra, exact scale identities, strict interior gap and finite-factor limits. This matrix owner consumes those original names directly in root_power, native_two_scale, actual_roots, actual_power, weightedColumns_limit and the strict density witnesses.")),
            Node("matrix", "Complex qubit matrices", Equal(Id("Mat"), Matrix()),
                "Real symmetric witnesses are represented as complex matrices with zero imaginary entries.",
                "Mat", DescribeRole.Definition),
            Node("density", "The exact density domain", DensityFormula(),
                "Density requires strict positive definiteness, complex trace exactly one, every entry real, and transpose symmetry. No singular witness is used.",
                "Density", DescribeRole.Definition),
            Node("mean", "The native unweighted mean", MeanFormula(),
                "The base-first geometricMean is the existing library operation. For SPD A and B and real p, put X=A^p and Y=B^p. The native mean is X^(-1/2) sqrt(X^(1/2) Y X^(1/2)) X^(-1/2). It is the unique strictly positive solution of L X L=Y. Square-root uniqueness proves this Riccati identification. Reversing A and B gives inverse(L).",
                "nativeMean", DescribeRole.Definition),
            Node("functional", "The UNTILDE spectral trace", TraceFormula(),
                "This is the powered quasi-extension in equation (2.4) of the original family (2.3), with the literal outer spectral 1/p power. Equations (2.5)--(2.6) define the different TILDE family. The Riccati identity gives S(1-alpha,p,B,A)=S(alpha,p,A,B) before taking the outer power. Unitary covariance follows from InverseGeometricIdentification.unitary_rpow.",
                "spectralTrace", DescribeRole.Definition),
            Node("diagonal", "Diagonal density path", DiagonalFormula(),
                "For 0<t<1, A(t)=diag(1-t,t) is strictly positive, real symmetric and has trace one.",
                "diagonalState", DescribeRole.Definition),
            Node("balanced", "Balanced density path", BalancedFormula(),
                "For 0<s<1/2, B(s)=(1/2)[[1,1-2s],[1-2s,1]] has eigenvalues 1-s and s and is a real symmetric strictly positive density matrix. Conjugation by J=[[0,1],[1,0]] sends A(t) to A(1-t) and fixes B(s), so the two endpoint functional values agree.",
                "balancedState", DescribeRole.Definition),
            Node("geometry", "Literal affine, faithful and noncommuting witnesses", GeometryFormula(),
                "The affine coefficient is ell=(tau-s^2)/(1-2s^2). Every matrix in the three functional evaluations is a density matrix, and each varying diagonal matrix fails to commute with B(s). Below the midpoint B(s) is fixed; above the midpoint the complement identity fixes B(s) as the first argument.",
                "WitnessGeometry", DescribeRole.Definition),
            Node("violation", "Constructive violation for every admissible pair", ViolationFormula(),
                "For beta=alpha below the midpoint and beta=1-alpha above it, choose tau=min(1/4,(2^(-beta/(1-beta))-1/2)^(1/p)). Then tau>0 and m(tau)=((1-tau)^p+tau^p)/2 has m(tau)^((1-beta)/p)<2^(-beta/p). At fixed A(tau), the rank-one second-input limit is m(tau)^((1-beta)/p). The simultaneous endpoint A(s^2),B(s) has limit 2^(-beta/p). A single sufficiently small positive s gives the strict gap and s^2<tau. Exact affine coordinates and equal endpoint values give the displayed Jensen violation.",
                "off_midpoint_violation", DescribeRole.Theorem,
                "For alpha>0 and p>0, every fixed SPD matrix A and every eventually SPD net F converging to P=(1/2)[[1,1],[1,1]] satisfy the following limit. Put X=A^p and m=Re(X11+X12+X21+X22)/2. Positivity of the quadratic form at (1,1) proves m>0, and entry algebra gives P X P=m P. Square-root uniqueness yields sqrt(X^(1/2) P X^(1/2))=m^(-1/2) X^(1/2) P X^(1/2). Consequently the native mean tends to m^(-1/2) P and S(alpha,p,A,F) tends to m^((1-alpha)/p). Only positive powers of the varying matrices are continued across the rank-one limit; the inverse of X remains fixed.",
                "Write z=s^(p/2), x=(1-s^2)^p, a=((1-s)^p+z^2)/2, b=((1-s)^p-z^2)/2, e=((1-s^2)(1-s))^(p/2), and c=sqrt(a(x+z^4)+2z^3 e). The exact native mean has entries u=(a+z^3 e/x)/c, v=b/c, w=(a+e/z)/c. Entry algebra and Riccati uniqueness identify this actual matrix, with z(uw-v^2)=e/x. The ordered scalar roots m,M satisfy z M -> sqrt(2) and m=(e/x)/(z M) -> k=1/sqrt(2).",
                "For rho=sqrt(((u-w)/2)^2+v^2) and H=(L-(u+w)I/2)/rho, entry algebra proves H*=H and H^2=I. The existing CumulantRenyiDataProcessingRefutation.two_point_cfc gives L^beta=m^beta I+gamma(L-mI). With C=z M and q=z m/C, the exact slope is gamma=C^(beta-1) z^(1-beta)(1-q^beta)/(1-q). All factors have finite limits and gamma -> 0 because 0<beta<1.",
                "For E=L^beta A(s^2)^(p/2), its entries are d(m^beta+gamma(u-m)), z^2 gamma v, d gamma v, and z^2 m^beta+z gamma(z w-z m), where d=(1-s^2)^(p/2). Thus E -> diag(k^beta,0), and E E* -> 2^(-beta)diag(1,0). Positive-power continuity across zero uses CFC.continuousOn_nnrpow with nnrpow_eq_rpow; continuity of the divergent geometric mean is never required. The outer 1/p spectral power and real trace give 2^(-beta/p)."),
            Node("claim", "Concavity at any off-midpoint parameter", ClaimFormula(),
                "The closed Prop claim asserts existence of at least one off-midpoint admissible pair with joint concavity on the exact density domain. Negating this existential excludes every such pair.",
                "claim", DescribeRole.Definition),
            Node("result", "No off-midpoint pair is jointly concave", new Formula.Not(Id("claim")),
                "The all-parameter constructive theorem contradicts joint concavity along the literal affine segment with its fixed argument. The midpoint alpha=1/2 is outside this theorem's parameter range.",
                "result", DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Quantum/Hiai/SpectralNonconcavityScalars"))]));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration, DescribeRole role, params string[] details)
    {
        var blocks = new List<DocumentBlock> { Paragraph(Text(prose)) };
        blocks.AddRange(details.Select(value => Paragraph(Text(value))));
        return Describe.Lean(DescribeId.Create("untilde-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks([.. blocks]), role);
    }

    private static Formula Id(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(Id("C")));
    private static Formula Matrix() => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Complex);
    private static Formula Group(Formula f) => Seq(Open, f, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula NeqOf(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula And(params Formula[] fs) => fs.Aggregate((a,b) =>
        new Formula.Logic(Group(a), FormulaLogicOperator.And, Group(b)));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Group(a), FormulaLogicOperator.Implies, Group(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Group(b));
    private static Formula All(string n, Formula type, Formula body) => Seq(Forall, Sp, Id(n), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string n, Formula type, Formula body) => Seq(Exists, Sp, Id(n), Colon, Sp, type, Comma, Sp, body);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Half => new Formula.Fraction(D(1), D(2));
    private static Formula Pow(Formula a, Formula r) => Call("rpow", a, r);
    private static Formula A(Formula t) => Call("diagonalState", t);
    private static Formula B(Formula s) => Call("balancedState", s);
    private static Formula S(Formula a, Formula p, Formula x, Formula y) => Call("spectralTrace", a,p,x,y);

    private static Formula DensityFormula()
    {
        var a=Id("A");
        return All("A", Matrix(), Iff(Call("Density",a), And(Call("PosDef",a),
            Equal(Call("trace",a),D(1)), All("i",Call("Fin",D(2)), All("j",Call("Fin",D(2)),
                Equal(Call("im",new Formula.Apply(a,[Id("i"),Id("j")])),D(0)))),
            Equal(Call("transpose",a),a))));
    }
    private static Formula MeanFormula() => All("p",Real, All("A",Matrix(), All("B",Matrix(),
        Equal(Call("nativeMean",Id("p"),Id("A"),Id("B")), Call("geometricMean",Half,
            Pow(Id("A"),Sub(D(0),Id("p"))),Pow(Id("B"),Id("p")))))));
    private static Formula TraceFormula()
    {
        var a=Id("alpha"); var p=Id("p"); var x=Id("A"); var y=Id("B");
        var l=Call("nativeMean",p,x,y);
        return All("alpha",Real,All("p",Real,All("A",Matrix(),All("B",Matrix(), Equal(S(a,p,x,y),
            Call("Re",Call("trace",Pow(Mul(Mul(Pow(l,a),Pow(x,p)),Pow(l,a)),new Formula.Fraction(D(1),p)))))))));
    }
    private static Formula DiagonalFormula() => All("t",Real,
        Equal(A(Id("t")),Call("diag",Sub(D(1),Id("t")),Id("t"))));
    private static Formula BalancedFormula() => All("s",Real,
        Equal(B(Id("s")),Call("sym",Half,Sub(Half,Id("s")),Half)));
    private static Formula GeometryFormula()
    {
        var t=Id("tau"); var s=Id("s"); var l=Id("ell"); var q=Mul(s,s);
        var a=A(q); var b=A(Sub(D(1),q)); var c=A(t); var d=B(s);
        return All("tau",Real,All("s",Real,All("ell",Real,Iff(Call("WitnessGeometry",t,s,l),
            And(Less(D(0),t),Less(t,Half),Less(D(0),s),Less(s,Half),Less(q,t),Less(D(0),l),Less(l,Half),
                Call("Density",a),Call("Density",b),Call("Density",c),Call("Density",d),
                Equal(c,Add(Mul(Sub(D(1),l),a),Mul(l,b))),
                NeqOf(Mul(a,d),Mul(d,a)),NeqOf(Mul(b,d),Mul(d,b)),NeqOf(Mul(c,d),Mul(d,c)))))));
    }
    private static Formula Conditions(Formula a, Formula p) =>
        And(Less(D(0),a),Less(a,D(1)),NeqOf(a,Half),Less(D(0),p));
    private static Formula ViolationFormula()
    {
        var a=Id("alpha"); var p=Id("p"); var t=Id("tau"); var s=Id("s"); var l=Id("ell");
        var x=A(Mul(s,s)); var y=A(Sub(D(1),Mul(s,s))); var c=A(t); var d=B(s);
        var low=Less(S(a,p,c,d),Add(Mul(Sub(D(1),l),S(a,p,x,d)),Mul(l,S(a,p,y,d))));
        var high=Less(S(a,p,d,c),Add(Mul(Sub(D(1),l),S(a,p,d,x)),Mul(l,S(a,p,d,y))));
        return All("alpha",Real,All("p",Real,Implies(Conditions(a,p),Some("tau",Real,Some("s",Real,Some("ell",Real,
            And(Call("WitnessGeometry",t,s,l),Implies(Less(a,Half),low),Implies(Less(Half,a),high))))))));
    }
    private static Formula ClaimFormula() => Iff(Id("claim"),Some("alpha",Real,Some("p",Real,
        And(Conditions(Id("alpha"),Id("p")),Call("JointlyConcaveOn",Call("Density"),Call("Density"),
            Call("spectralTrace",Id("alpha"),Id("p")))))));
}
