using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeightedLegalPathTemperleyLiebDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite symmetric weighted legal paths carry the exact local Temperley-Lieb projections.",
        H("Weighted Legal-Path Temperley-Lieb Relations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-legal-path-temperley-lieb"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb."
                        + "weighted_legal_path_temperley_lieb"),
                H("Weighted path projections satisfy all four local relations"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let L be any finite label type and R a symmetric Boolean adjacency "
                            + "relation, including possible self-loops. Every label has a "
                            + "strictly positive real weight d, delta is strictly positive, "
                            + "and the sum of d(b) over R(a,b) equals delta times d(a) "
                            + "for every a. Fix any path length n and endpoints s,t. "
                            + "The path basis contains precisely the legal length-n paths "
                            + "from s to t and may be empty.")),
                    Paragraph(Text(
                        "For every interior i, P_i(x,y) is zero unless x and y agree "
                            + "outside i and x at i-1 equals x at i+1. In the remaining "
                            + "case its literal FT.12 coefficient is the complex cast of "
                            + "sqrt(d(x_i) * d(y_i)) / (delta * d(x_(i-1))). "
                            + "This is the source's square root of the product, with no "
                            + "rescaling or normalization of P_i.")),
                    Paragraph(Text(
                        "The theorem establishes self-adjointness and idempotence at every "
                            + "interior index, the forward adjacent triple product whenever "
                            + "i+1 is interior, and commutation for both ordered cases of "
                            + "distance at least two. Its local replacement equivalence "
                            + "identifies a legal fiber with the neighbors of its common "
                            + "flank; the proof also establishes the adjacent unique "
                            + "survivor and the distant locality argument. No nonempty "
                            + "path-space premise is used."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Application: Fibonacci three-setting tomography"), Blocks(
            Paragraph(Text(
                "Use labels 0=vacuum and 1=tau, adjacency R(c,d) iff c=1 or d=1, "
                    + "weights d(0)=1 and d(1)=phi, and delta=phi, where phi is the golden ratio. "
                    + "The fixed-endpoint carrier LegalPath R 3 0 1 has precisely the two ordered "
                    + "paths (0,1,0,1) and (0,1,1,1). Reindexing the coordinate orthonormal basis "
                    + "by these paths identifies the source H_3^tau with C^2. The literal "
                    + "pathProjection entries at positions 1 and 2 are P=diag(1,0) and "
                    + "Q=[[r^2,b],[b,r]], with r=1/phi>0, s=sqrt(r)>0, and b=r*s>0. "
                    + "The Perron equation is phi=phi*1 at label 0 and 1+phi=phi^2 at label 1; "
                    + "the weighted-path theorem therefore supplies the actual projection laws. "
                    + "In the fixed gauge F=[[r,s],[s,-r]], Q=F*P*F-adjoint. "
                    + "The permitted active pulse V=I+(i-1)P=diag(i,1) is unitary.")),
            Paragraph(Text(
                "For every real p,x,y with 0<=p<=1 and x^2+y^2<=p(1-p), keep the entire "
                    + "mixed-state matrix rho=[[p,x+i*y],[x-i*y,1-p]]. All three readouts use this "
                    + "same rho: m0=Tr(P*rho), m1=Tr(Q*rho), and m2=Tr(Q*V*rho*V-adjoint). "
                    + "Writing h=r^2-r=1-2*r<0, they equal p, r+h*p+2*b*x, and r+h*p-2*b*y. "
                    + "Thus p=m0, x=(m1-r-h*m0)/(2*b), and y=(r+h*m0-m2)/(2*b), exactly FT.25. "
                    + "The sign in the scalarB correspondence is essential: "
                    + "rho=FourQubitParentConstruction.scalarB(1/2,(x,-y,p-1/2)). "
                    + "Its public scalarB_posSemidef_iff identifies precisely the full closed "
                    + "radius-1/2 ball, including all boundary states.")),
            Paragraph(Text(
                "For every epsilon>=0 and all three errors |eta_j|<=epsilon, invert the noisy "
                    + "readouts m+eta without imposing positivity on the reconstructed matrix. "
                    + "The coordinate errors are delta_p=eta0, delta_x=(eta1-h*eta0)/(2*b), and "
                    + "delta_y=(h*eta0-eta2)/(2*b). Since (1-h)/(2*b)=sqrt(phi), their absolute "
                    + "values are at most epsilon, sqrt(phi)*epsilon, and sqrt(phi)*epsilon. "
                    + "Applying TraceNorm.transitionMass_sq and traceNorm_nonneg to this same "
                    + "trace-zero matrix difference gives half its trace norm equal to "
                    + "sqrt(delta_p^2+delta_x^2+delta_y^2). Consequently it is at most "
                    + "kappa*epsilon, where kappa=sqrt(1+2*phi), as in FT.26. "
                    + "These are applications and coefficient normalizations of existing "
                    + "matrix and norm results; no new mathematical declaration is required.")),
            Paragraph(Text(
                "For eta0=eta1=eta2=epsilon, the three coordinate errors are simultaneously "
                    + "epsilon, sqrt(phi)*epsilon, and -sqrt(phi)*epsilon, and half the trace norm "
                    + "is exactly kappa*epsilon. At the true state rho=I/2 all three exact "
                    + "readouts are 1/2. For every 0<=epsilon<=1/(4*kappa), the noisy readouts "
                    + "are in [0,1], the reconstructed Bloch radius is at most 1/4, and the "
                    + "reconstructed trace-one matrix is positive semidefinite. Its actual "
                    + "P,Q,V readouts equal those same noisy values. This is a positive physical "
                    + "neighborhood, so any constant smaller than kappa fails even there; "
                    + "sharpness concerns one simultaneously realizable state and error triple.")),
            Paragraph(Text(
                "For arbitrary raw reconstruction project u=(p_hat-1/2,x_hat,y_hat) onto the "
                    + "actual Euclidean closed ball of radius 1/2. Mathlib's "
                    + "exists_norm_eq_iInf_of_complete_convex supplies a nearest point v. Its "
                    + "norm_eq_iInf_iff_real_inner_le_zero characterization gives "
                    + "inner(u-v,w-v)<=0 for every true ball point w. Expanding the squared "
                    + "distance yields norm(v-w)<=norm(u-w). The signed coordinate permutation "
                    + "(u0,u1,u2) maps to (u1,-u2,u0), preserving this distance and the ball. "
                    + "Return v to the same matrix family as rho(v0+1/2,v1,v2). It is positive "
                    + "semidefinite with trace one, and its half trace-norm error to every true "
                    + "state cannot exceed the raw error. Hence FT.26 survives this closed-ball "
                    + "projection. The readouts throughout are expectations from independent "
                    + "preparations; finite-sample statistics require a separate error budget.")))))));


    private static Formula Call(string name, params Formula[] args)
    {
        var nameParts = name.Split('.');
        var operatorParts = new List<Formula> { F.Id(nameParts[0]) };
        for (var part = 1; part < nameParts.Length; part++)
        {
            operatorParts.Add(Dot);
            operatorParts.Add(F.Id(nameParts[part]));
        }

        var items = new List<Formula> { Operatorname, Grp([.. operatorParts]), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);

    private static Formula At(Formula function, Formula index) => Apply(function, index);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(params Formula[] terms)
    {
        var result = terms[^1];
        for (var index = terms.Length - 2; index >= 0; index--)
            result = new Formula.Logic(terms[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula labels = F.Id("L");
        Formula relation = F.Id("R");
        Formula weights = F.Id("d");
        Formula delta = Delta;
        Formula length = F.Id("n");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula p = F.Id("P");
        Formula pi = Sub(p, i);
        Formula pj = Sub(p, j);
        Formula next = Sub(p, Seq(i, Plus, D(1)));
        Formula interior = Seq(D(1), Le, Sp, i, Lt, length);
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula k = F.Id("k");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula path = Call("LegalPath", relation, length, F.Id("s"), F.Id("t"));
        Formula pathFunctionType = new Formula.TypeArrow(
            Call("Fin", Seq(length, Plus, D(1))), labels);
        Formula pathAdjacency = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            Call("Fin", length),
            Apply(relation,
                At(x, k),
                At(x, Seq(k, Plus, D(1)))));
        Formula pathBody = And(
            Equal(At(x, D(0)), F.Id("s")),
            Equal(At(x, length), F.Id("t")),
            pathAdjacency);
        Formula pathDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, path, Colon, Sp, F.Id("Type"),
            Sp, Eq, Sp, OpenBrace, x, Colon, Sp, pathFunctionType, Sp, Bar, Sp,
            pathBody, CloseBrace, Semi, Sp);
        Formula support = And(
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("k"),
                Call("Fin", Seq(length, Plus, D(1))),
                Implies(
                    NotEqual(k, i),
                    Equal(At(x, k), At(y, k)))),
            Equal(
                At(x, Seq(i, Minus, D(1))),
                At(x, Seq(i, Plus, D(1)))));
        Formula coefficient = Call(
            "Complex.ofReal",
            new Formula.Fraction(
                Seq(Sqrt, Grp(new Formula.Binary(
                    At(weights, At(x, i)),
                    FormulaBinaryOperator.Multiply,
                    At(weights, At(y, i))))),
                new Formula.Binary(
                    delta,
                    FormulaBinaryOperator.Multiply,
                    At(weights, At(x, Seq(i, Minus, D(1)))))));
        Formula piecewise = Seq(
            Open, Begin, Grp(F.Id("cases")),
            coefficient, Sp, Amp, Sp, F.Text, Grp(F.Id("if")), Sp, Open, support, Close,
            RowBreak,
            D(0), Sp, Amp, Sp, F.Text, Grp(F.Id("otherwise")),
            End, Grp(F.Id("cases")), Close);
        Formula projectionDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, pi, Colon, Sp,
            Call("Matrix", path, path, complex), Comma, Sp,
            i, InMacro, Sp, natural, Comma, Sp, interior, Comma, Sp,
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [
                    new Formula.BoundVariable(FormulaIdentifier.Create("x"), path),
                    new Formula.BoundVariable(FormulaIdentifier.Create("y"), path),
                ],
                Equal(Apply(pi, x, y), piecewise)),
            Semi, Sp);
        Formula pf = Seq(
            Forall, Sp, a, InMacro, Sp, labels, Comma, Sp,
            D(0), Lt, Sub(weights, a), Sp, Land, Sp,
            Sum, Underscore, Grp(b, Colon, Sp, Call("R", a, b)), Sp,
            Sub(weights, b), Eq, delta, Sp, Sub(weights, a));
        Formula adjacent = Seq(D(1), Le, Sp, i, Comma, Sp, i, Plus, D(1), Lt, length);
        Formula distant = Seq(
            D(1), Le, Sp, i, Lt, length, Comma, Sp,
            D(1), Le, Sp, j, Lt, length, Comma, Sp,
            i, Plus, D(2), Le, Sp, j, Sp, Lor, Sp, j, Plus, D(2), Le, Sp, i);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, labels, Colon, Sp, Operatorname, Grp(F.Id("Finite")), Comma, Sp,
            relation, Colon, Sp, labels, Sp, To, Sp, labels, Sp, To, Sp,
            Operatorname, Grp(F.Id("Prop")), Comma, Esc,
            Call("Symmetric", relation), Comma, Sp,
            weights, Colon, Sp, labels, Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(0), Lt, delta, Comma, Sp, pf, Comma, Esc,
            Forall, Sp, length, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
            F.Id("s"), Comma, Sp, F.Id("t"), InMacro, Sp, labels, Comma, RowBreak,
            pathDefinition, RowBreak,
            projectionDefinition, RowBreak,
            Open, Forall, Sp, i, Comma, Sp, interior, Sp, Rightarrow, Sp,
            Call("conjTranspose", pi), Eq, pi, Sp, Land, Sp, pi, pi, Eq, pi, Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, i, Comma, Sp, adjacent, Sp, Rightarrow, Sp,
            pi, next, pi, Eq, delta, Caret, Grp(Minus, D(2)), pi, Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, i, Comma, Sp, j, Comma, Sp, distant, Sp, Rightarrow, Sp,
            pi, pj, Eq, pj, pi, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
