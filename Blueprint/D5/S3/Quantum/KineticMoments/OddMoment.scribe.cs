using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.KineticMoments;

internal sealed class OddMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/KineticMoments/OddMoment.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/tolias2025kineticmoments");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The kinetic contribution obeys the all-order odd-moment formula for every isotropic momentum distribution with finite required moments.", H("Kinetic odd frequency moments"), Blocks(
            Node("shift", "Single-particle momentum shift", Disp(All(N,Nat,All(J,Call("Fin",N),All(F.Id("v"),Vec,Eqn(Call("shift",J,F.Id("v")),Apply(Qualified("LinearMap","funLeft"),Cx,Cx,Lam(P,Config,Apply(Qualified("Function","update"),P,J,Add(Apply(P,J),F.Id("v")))))))))),
                "The momentum-space construction acts on every complex-valued configuration function. It replaces only particle j by p_j + v. The linear map is Mathlib LinearMap.funLeft; no regularity or operator-domain restriction is imposed.", false),
            Node("rho", "Density operator", Disp(All(N,Nat,All(Hbar,R,All(Q,Vec,Eqn(Call("rho",N,Hbar,Q),Sum(J,Call("Fin",N),Call("shift",J,Call("smul",Hbar,Q)))))))),
                "Sec. 2.4, p. 5, gives the microscopic density operator and its Hermitian conjugate as sums of opposite position exponentials. In the momentum convention these are sums of pullbacks by +hbar q and -hbar q respectively. Multiplication of a real scalar and a vector here denotes real scalar multiplication.", true),
            Node("rhoDag", "Conjugate density operator", Disp(All(N,Nat,All(Hbar,R,All(Q,Vec,Eqn(Call("rhoDag",N,Hbar,Q),Sum(J,Call("Fin",N),Call("shift",J,Negate(Call("smul",Hbar,Q))))))))),
                "Sec. 2.4, p. 5, gives the microscopic density operator and its Hermitian conjugate as sums of opposite position exponentials. In the momentum convention these are sums of pullbacks by +hbar q and -hbar q respectively. Multiplication of a real scalar and a vector here denotes real scalar multiplication.", true),
            Node("energy", "Kinetic energy multiplier", Disp(All(N,Nat,All(M,R,All(P,Config,Eqn(Call("energy",M,P),Sum(J,Call("Fin",N),Div(Pow(Norm(Apply(P,J)),D(2)),Twice(M)))))))),
                "The source substitutes the kinetic energy operator K = sum_i p_i^2/(2m) (Sec. 2.4, p. 5). The squared momentum is the Euclidean norm squared, and each term is divided by twice the common mass.", true),
            Node("kinetic", "Kinetic operator", Disp(All(N,Nat,All(M,R,Eqn(Call("kinetic",N,M),MuLeft(Lam(P,Config,Cast(Call("energy",M,P),Cx))))))),
                "The kinetic Hamiltonian acts by multiplication by the real energy, embedded in the complex numbers. This uses the existing LinearMap.mulLeft construction.", true),
            Node("delta", "One kinetic commutator nest", Disp(All(N,Nat,All(M,R,All(F.Id("X"),Endomorphisms,Eqn(Call("delta",M,F.Id("X")),Sub(Mul(F.Id("X"),Call("kinetic",N,M)),Mul(Call("kinetic",N,M),F.Id("X")))))))),
                "Sec. 2.2, p. 3: \"The pure kinetic contribution to the odd dynamic structure factor frequency moments of arbitrary order is obtained from Eq.(4) by considering only the kinetic part of the Hamiltonian, i.e. setting Ĥ ≡ K̂.\" Thus the first H nest and all later K nests coincide. delta(X) is [X,K], with this order.", true),
            Node("C", "The split nested commutator", Disp(All(N,Nat,All(Hbar,R,All(M,R,All(Q,Vec,All(K,Nat,All(Ell,Nat,Eqn(Call("C",N,Hbar,M,Q,K,Ell),Apply(Qualified("Bracket","bracket"),Apply(Apply(Qualified("Function","iterate"),Call("delta",M),Apply(Qualified("Nat","sub"),Order,Ell)),Call("rho",N,Hbar,Q)),Apply(Apply(Qualified("Function","iterate"),Call("delta",M),Ell),Call("rhoDag",N,Hbar,Q))))))))))),
                "Equation (9), p. 3, assigns 2k+1-ell nests to rho and ell nests to rhoDag. iterate denotes Function.iterate; the sub in its natural-number exponent is Nat.sub (truncated subtraction). The later hypothesis ell ≤ 2k+1 ensures the two counts sum to 2k+1. Bracket.bracket is the ring commutator XY-YX.", true),
            Node("a", "Recoil energy", Disp(All(Hbar,R,All(M,R,All(Q,Vec,Eqn(Call("a",Hbar,M,Q),Div(Mul(Pow(Hbar,D(2)),Pow(Norm(Q),D(2))),Twice(M))))))),
                "This recoil energy is the momentum-independent part of the energy difference under the shift hbar q.", false),
            Node("b", "Directional energy increment", Disp(All(N,Nat,All(Hbar,R,All(M,R,All(Q,Vec,All(J,Call("Fin",N),All(P,Config,Eqn(Call("b",Hbar,M,Q,J,P),Mul(Div(Hbar,M),Inner(Q,Apply(P,J))))))))))),
                "The linear increment depends on the same particle and momentum configuration as the kinetic energy. It is (hbar/m) times the real inner product q·p_j.", false),
            Node("F", "The real commutator multiplier", Disp(All(N,Nat,All(Hbar,R,All(M,R,All(Q,Vec,All(K,Nat,All(Ell,Nat,All(P,Config,Eqn(Multiplier,Mul(Pow(Negate(D(1)),Ell),Sum(J,Call("Fin",N),Sub(Pow(Add(Call("b",Hbar,M,Q,J,P),Call("a",Hbar,M,Q)),Order),Pow(Sub(Call("b",Hbar,M,Q,J,P),Call("a",Hbar,M,Q)),Order))))))))))))),
                "This multiplier records the two surviving same-particle shift products. All products with different particle labels cancel. It is defined independently of the nested operator expression.", false),
            Node("FiniteTopMoment", "Finite highest required moment", Disp(All(N,Nat,All(Nu,Measure,All(K,Nat,Iff(Call("FiniteTopMoment",Nu,K),All(J,Call("Fin",N),Call("Integrable",Lam(P,Config,Pow(Norm(Apply(P,J)),Twice(K))),Nu))))))),
                "The finite 2k-th moment is assumed for each particle. Under a probability measure all lower even moments follow by domination with 1+|p_j|^(2k).", false),
            Node("momentumMoment", "Per-particle radial average", Disp(All(N,Nat,All(Nu,Measure,All(I,Nat,Eqn(Call("momentumMoment",Nu,I),Mul(Pow(Cast(N,R),Negate(D(1))),Sum(J,Call("Fin",N),Integral(MomentPower)))))))),
                "The source averages even powers of momentum over the exact distribution (Sec. 2.3, p. 5). The per-particle convention is N^-1 times the sum of the individual radial integrals, rather than a moment of the total many-particle kinetic energy.", true),
            Node("prefactor", "The complex sum-rule prefactor", Disp(All(N,Nat,All(K,Nat,All(Ell,Nat,All(Hbar,R,Eqn(Call("prefactor",N,K,Ell,Hbar),Mul(Mul(Pow(Parenthesized(Seq(Negate(D(1)),Colon,Cx)),Add(Add(K,Ell),D(1))),Div(Cast(Hbar,Cx),Mul(D(2),Cast(N,Cx)))),Pow(Parenthesized(Div(Qualified("Complex","I"),Cast(Hbar,Cx))),Add(Twice(K),D(2)))))))))),
                "Equation (9), p. 3, gives (-1)^(k+ell+1) hbar/(2N) (imath/hbar)^(2k+2). Its arithmetic is complex, and N and hbar are embedded in the complex numbers before division.", true),
            Node("target", "The conjectured odd moment", Disp(All(N,Nat,All(Hbar,R,All(M,R,All(Q,Vec,All(Nu,Measure,All(K,Nat,Eqn(Call("target",Hbar,M,Q,Nu,K),Mul(Div(Pow(Parenthesized(Div(Mul(Hbar,Pow(Norm(Q),D(2))),Twice(M))),Order),Add(Twice(Cast(K,R)),D(2))),SumOver(I,Apply(Qualified("Finset","range"),Add(K,D(1))),Mul(Mul(Cast(Apply(Qualified("Nat","choose"),Add(Twice(K),D(2)),Add(Twice(I),D(1))),R),Pow(Parenthesized(Div(D(2),Mul(Hbar,Norm(Q)))),Twice(I))),Call("momentumMoment",Nu,I)))))))))))),
                "Equation (16), Sec. 2.3, p. 5, is encoded literally, with q the norm of the real wave vector, all divisions real and the finite sum indexed by Finset.range(k+1), hence 0 ≤ i ≤ k. choose is Nat.choose. The natural sum indices are embedded in the reals before the denominators are formed.", true),
            Node("claim", "The Tolias-Dornheim-Vorberger conjecture", Disp(Iff(F.Id("claim"),ClaimBody())),
                "Sec. 2.3, p. 5: \"Therefore, our conjecture states that the following result holds for the interacting uniform electron gas\" (Eq. (16)), followed by \"where k is an arbitrary non-negative integer.\" Encoding: N ≥ 1; hbar>0; m>0; q ≠ 0; every k and every ell ≤ 2k+1; the exact operator multiplier identity; every simultaneous-SO(3)-invariant probability measure with finite highest required per-particle moment. The average of the multiplication operator is the integral of its multiplier. The kinetic prescription H ≡ K is the source sentence in Sec. 2.2, p. 3. The statement constructs no thermodynamic-limit state, assumes moment finiteness and makes no assertion about the full non-kinetic moment.", true),
            Node("result", "All odd kinetic moments satisfy the conjecture", Disp(F.Id("claim")),
                "The operator identity reduces the kinetic average to an odd binomial difference. Isotropic averaging produces 1/(2i+1); Nat.add_one_mul_choose_eq transfers this factor to the denominator 2k+2. Kinematic powers and the complex sum-rule prefactor then give Eq. (16) for every split. The proof imposes no particle-statistics condition: it applies whenever the stated momentum measure exists and is isotropic with finite moments.", false, DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("tolias-dornheim-vorberger-2025-kinetic-odd-moments"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool literature, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("kinmom-oddmoment-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula N => F.Id("N");
    private static Formula Hbar => F.Id("hbar");
    private static Formula M => F.Id("m");
    private static Formula Q => F.Id("q");
    private static Formula P => F.Id("P");
    private static Formula J => F.Id("j");
    private static Formula K => F.Id("k");
    private static Formula Ell => F.Id("ell");
    private static Formula Nu => F.Id("nu");
    private static Formula I => F.Id("i");
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Cx => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Vec => Call("EuclideanSpace", R, Call("Fin", D(3)));
    private static Formula Config => Seq(Parenthesized(Call("Fin", N)), Sp, To, Sp, Vec);


    private static Formula Measure => Call("Measure", Parenthesized(Config));

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot,
        Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula All(Formula x, Formula t, Formula body) => Seq(Forall, Sp, x, Colon, Sp, t, Comma, Sp, body);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);

    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula e) => new Formula.Power(x, e);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Negate(Formula x) => new Formula.Negate(x);
    private static Formula Cast(Formula x, Formula t) => Parenthesized(Seq(Call("val", x), Colon, Sp, t));
    private static Formula Lam(Formula x, Formula t, Formula body) => Parenthesized(Seq(x, Colon, Sp, t, Sp, Mapsto, Sp, body));
    private static Formula SumOver(Formula x, Formula set, Formula body) => Seq(F.Sum, Underscore,
        Grp(x, Sp, InMacro, Sp, set), Sp, Parenthesized(body));
    private static Formula Sum(Formula x, Formula t, Formula body) => Seq(F.Sum, Underscore,
        Grp(x, Colon, t), Sp, Parenthesized(body));
    private static Formula Integral(Formula body) => Seq(Int, Underscore, Grp(P,Colon,Config), Sp, body, Sp, Mathrm, Grp(F.Id("d")), Sp, Nu);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert, Sp);

    private static Formula Twice(Formula x) => Mul(D(2), x);
    private static Formula Order => Add(Twice(K), D(1));
    private static Formula MuLeft(Formula f) => Apply(Qualified("LinearMap", "mulLeft"), Cx, f);
    private static Formula MomentPower => Pow(Norm(Apply(P,J)), Twice(I));
    private static Formula Multiplier => Call("F", Hbar,M,Q,K,Ell,P);
    private static Formula OperatorEquality => Eqn(Call("C",N,Hbar,M,Q,K,Ell),
        MuLeft(Lam(P,Config,Cast(Multiplier,Cx))));



    private static Formula ClaimBody() => All(N,Nat,Imp(Leq(D(1),N),All(Hbar,R,All(M,R,
        Imp(Less(D(0),Hbar),Imp(Less(D(0),M),All(Q,Vec,Imp(Ne(Q,D(0)),
            All(K,Nat,All(Ell,Nat,Imp(Leq(Ell,Order),And(OperatorEquality,
                All(Nu,Measure,Imp(Call("IsProbabilityMeasure",Nu),Imp(Call("IsIsotropic",Nu),
                    Imp(Call("FiniteTopMoment",Nu,K),Eqn(
                        Mul(Call("prefactor",N,K,Ell,Hbar),Cast(Integral(Multiplier),Cx)),
                        Cast(Call("target",Hbar,M,Q,Nu,K),Cx))))))))))))))))));

    private static Formula States => Seq(Parenthesized(Config), Sp, To, Sp, Cx);
    private static Formula Endomorphisms => Apply(Qualified("Module", "End"), Cx, Parenthesized(States));
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Inner(Formula x, Formula y) => Seq(Langle, Sp, x, Comma, y, Rangle, Sp);
}
