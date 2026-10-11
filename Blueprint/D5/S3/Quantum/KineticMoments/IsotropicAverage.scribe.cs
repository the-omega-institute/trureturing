using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.KineticMoments;

internal sealed class IsotropicAverageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/KineticMoments/IsotropicAverage.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/tolias2025kineticmoments");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A weighted-moment recurrence determines every isotropic directional even moment.", H("Isotropic even directional averages"), Blocks(
            Node("simultaneousRotation", "Rotate every momentum together", Disp(All(N,Nat,All(F.Id("R"),Rotations,All(P,Config,Eqn(Call("simultaneousRotation",F.Id("R"),P),Lam(J,Call("Fin",N),Apply(F.Id("R"),Apply(P,J)))))))),
                "A single real linear isometry is applied to every particle. Correlations between particles are preserved; independent rotations are not assumed.", false),
            Node("IsIsotropic", "Simultaneous SO(3) invariance", Disp(All(N,Nat,All(Nu,Measure,Iff(Call("IsIsotropic",Nu),All(F.Id("R"),Rotations,Imp(Eqn(Apply(Qualified("LinearMap","det"),Seq(F.Id("R"),Dot,F.Id("toLinearEquiv"),Dot,F.Id("toLinearMap"))),D(1)),Call("MeasurePreserving",Call("simultaneousRotation",F.Id("R")),Nu,Nu))))))),
                "Isotropy means that every determinant +1 linear isometry preserves the momentum-configuration measure. Reflections of determinant -1 are not assumed. Neither a probability normalization nor a moment bound is part of this predicate.", false),
            Node("integrable_directional", "Radial moment controls its directional moment", Disp(All(N,Nat,All(Nu,Measure,All(J,Call("Fin",N),All(I,Nat,All(Q,Vec,Imp(Call("Integrable",Lam(P,Config,MomentPower),Nu),Call("Integrable",Lam(P,Config,Pow(Inner(Q,Apply(P,J)),Twice(I))),Nu)))))))),
                "The Cauchy-Schwarz inequality bounds |q·p_j|^(2i) by |q|^(2i)|p_j|^(2i). Radial integrability therefore suffices. This estimate controls the finite sums inside the odd moment integral.", false, DescribeRole.Theorem),
            Node("isotropic_average", "Exact isotropic directional average", Disp(All(N,Nat,All(Nu,Measure,All(J,Call("Fin",N),All(I,Nat,All(Q,Vec,Imp(Call("IsIsotropic",Nu),Imp(Call("Integrable",Lam(P,Config,MomentPower),Nu),Eqn(Integral(Pow(Inner(Q,Apply(P,J)),Twice(I))),Div(Mul(Pow(Norm(Q),Twice(I)),Integral(MomentPower)),Add(Twice(Cast(I,R)),D(1)))))))))))),
                "The weighted directional moments are even, homogeneous and rotation invariant, so they depend only on |q|. Comparing the second coefficient in the polynomial for e_0+t e_l and summing all three coordinates gives the weighted recurrence. Induction yields the factor 1/(2i+1). The result applies to any isotropic measure with the stated integrable moment, including q=0 and i=0; it does not require a probability measure.", false, DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool literature, DescribeRole role = DescribeRole.Definition) => Describe.Lean(
        DescribeId.Create("kinmom-isotropicaverage-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula N => F.Id("N");


    private static Formula Q => F.Id("q");
    private static Formula P => F.Id("P");
    private static Formula J => F.Id("j");


    private static Formula Nu => F.Id("nu");
    private static Formula I => F.Id("i");
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Vec => Call("EuclideanSpace", R, Call("Fin", D(3)));
    private static Formula Config => Seq(Parenthesized(Call("Fin", N)), Sp, To, Sp, Vec);


    private static Formula Measure => Call("Measure", Parenthesized(Config));
    private static Formula Rotations => Call("LinearIsometryEquiv", R, Vec, Vec);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot,
        Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);




    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula All(Formula x, Formula t, Formula body) => Seq(Forall, Sp, x, Colon, Sp, t, Comma, Sp, body);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);

    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula e) => new Formula.Power(x, e);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);

    private static Formula Cast(Formula x, Formula t) => Parenthesized(Seq(Call("val", x), Colon, Sp, t));
    private static Formula Lam(Formula x, Formula t, Formula body) => Parenthesized(Seq(x, Colon, Sp, t, Sp, Mapsto, Sp, body));

    private static Formula Integral(Formula body) => Seq(Int, Underscore, Grp(P,Colon,Config), Sp, body, Sp, Mathrm, Grp(F.Id("d")), Sp, Nu);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert, Sp);
    private static Formula Inner(Formula x, Formula y) => Seq(Langle, Sp, x, Comma, y, Rangle, Sp);
    private static Formula Twice(Formula x) => Mul(D(2), x);


    private static Formula MomentPower => Pow(Norm(Apply(P,J)), Twice(I));





}
