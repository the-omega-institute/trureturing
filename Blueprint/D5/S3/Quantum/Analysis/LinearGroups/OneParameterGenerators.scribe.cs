using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.LinearGroups;

internal sealed class OneParameterGeneratorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a locally compact topological group G with a continuous injective homomorphism rho into the units of a real Banach algebra A, the elements X of A for which t -> exp(t X) lifts through rho to a continuous curve in G form a closed Lie subalgebra of A, and limits of normalized logarithms of elements tending to the identity are such generators.",
        H("One-Parameter Generators of a Locally Compact Group in a Banach Algebra"),
        Blocks(
            Node("generator", "IsOneParameterGenerator", "One-parameter generators",
                StatementSource.FromAuthor(GeneratorFormula()),
                DescribeRole.Definition,
                "Let A be a real normed algebra, written NormedRing(A) together with NormedAlgebra(R, A), let G be a group with a topology, and let rho be a group homomorphism from G into the group Units(A) of invertible elements of A. Here val denotes the inclusion of Units(A) into A, exp is the exponential series of A and smul(t, X) is the real multiple t X. An element X of A is a one-parameter generator for rho when the curve t -> exp(t X) of A lifts through rho to a continuous curve: there is a continuous map gamma from the real line to G with val(rho(gamma(t))) = exp(t X) for every real t. No continuity or injectivity of rho is part of the definition.",
                "When rho is injective a lift is unique when it exists and is a one-parameter subgroup of G. Indeed exp((s + t) X) = exp(s X) exp(t X) because s X and t X commute, so rho(gamma(s + t)) = rho(gamma(s) gamma(t)) and injectivity gives gamma(s + t) = gamma(s) gamma(t). The zero element is always a generator, lifted by the constant curve at the identity."),
            Node("smul", "smul", "Real multiples of a generator",
                StatementSource.FromAuthor(SmulFormula()),
                DescribeRole.Theorem,
                "If X is a one-parameter generator for rho, then so is the real multiple c X for every real c. In the same setting as the definition, with no further hypothesis on A, G or rho.",
                "If gamma lifts t -> exp(t X), then the reparametrized curve t -> gamma(t c) is continuous and lifts t -> exp(t c X) = exp(t (c X))."),
            Node("escape", "isOneParameterGenerator_of_mapClusterPt", "Escape lemma",
                StatementSource.FromAuthor(EscapeFormula()),
                DescribeRole.Theorem,
                "Let A be complete, let G be a locally compact topological group and let rho be continuous and injective. Let g be a sequence in G tending to the identity, and let Y be a sequence in A tending to 0 with val(rho(g(k))) = exp(Y(k)) for every k. Then every cluster point X of the sequence of directions smul(norm(Y(k))^(-1), Y(k)) is a one-parameter generator for rho. Indices with Y(k) = 0 contribute the direction 0, and 0 is a generator, so no nonvanishing hypothesis on Y is needed. No first countability and no separation axiom on G is assumed.",
                "The statement is the escape lemma of the closed-subgroup theorem of J. von Neumann for closed subgroups of the general linear group and of E. Cartan for closed subgroups of Lie groups. Here the closedness of a linear group is replaced by local compactness of G together with injectivity of rho, in three places. First, fix a compact neighbourhood V of the identity in G. On V the map rho reflects convergence: if points of V have images tending to rho(a), then they tend to a, because every cluster point of them lies in V and has image rho(a), hence equals a by injectivity. Second, there are a positive delta and a neighbourhood U of the identity such that the powers g^n stay in V whenever g lies in U, rho(g) = exp(Y) and n norm(Y) is at most delta; this follows by induction on n from a neighbourhood W of the identity with W W contained in V and from continuity of exp at 0.",
                "Third, pass to a subsequence along which the directions converge to X, with X different from 0 (the case X = 0 is the zero generator). For t in [0, delta] the powers of g(k) with exponent the integer part of t / norm(Y(k)) lie in V and their images tend to exp(t X), so a cluster point v of these powers in the compact set V satisfies val(rho(v)) = exp(t X); negative times are handled with the inverses of g(k) and the sequence -Y(k). Such lifts on [-delta, delta] extend to all real t by taking N-th powers of a lift of exp((t / N) X), and the lift is a homomorphism by injectivity. It is continuous at 0 because its values near 0 lie in V, where rho reflects convergence, and hence continuous everywhere.",
                "Local compactness of G cannot be dropped. Let G be the additive group of rational numbers with its usual topology, A the real numbers and rho(q) = exp(q). Then rho is continuous and injective, g(k) = 1 / (k + 1) tends to the identity 0 and Y(k) = 1 / (k + 1) satisfies the hypotheses, and every direction equals 1. But 1 is not a generator: a continuous curve from the real line into the rationals is constant, while exp(t) is not constant."),
            Node("closed", "isClosed_setOf_isOneParameterGenerator", "The set of generators is closed",
                StatementSource.FromAuthor(ClosedFormula()),
                DescribeRole.Theorem,
                "Let A be complete, let G be a locally compact topological group and let rho be continuous and injective. Then the set of one-parameter generators for rho is a closed subset of A.",
                "Since A is a metric space it suffices to consider a sequence of generators X(n) tending to X, with X different from 0. Let gamma(n) be lifts, fix a compact neighbourhood V of the identity and choose times s(n) with 0 < s(n) < 1 / (n + 1) and gamma(n)(s(n)) in V; such times exist since gamma(n)(0) is the identity and gamma(n) is continuous. The points gamma(n)(s(n)) of V have images exp(s(n) X(n)) tending to 1, so they tend to the identity because rho reflects convergence on V. Their logarithms s(n) X(n) tend to 0 and are eventually nonzero, and their directions tend to X / norm(X). The argument of the escape lemma, applied along this sequence, shows that X / norm(X) is a generator, and so is its multiple X."),
            Node("add", "add", "Sum of two generators",
                StatementSource.FromAuthor(AddFormula()),
                DescribeRole.Theorem,
                "Let A be complete, let G be a locally compact topological group and let rho be continuous and injective. If X and Y are one-parameter generators for rho, then so is X + Y.",
                "The proof rests on a velocity statement: if a curve c in G is continuous at 0 with val(rho(c(0))) = 1 and s -> val(rho(c(s))) has derivative D at 0, then D is a generator. The derivative of exp at 0 is the identity, so by the inverse function theorem exp has a local inverse near 1 that sends 1 to 0 and has the identity as derivative at 1. Composing it with s -> val(rho(c(s))) gives logarithms Z(s) with val(rho(c(s))) = exp(Z(s)) for small s, Z(0) = 0 and derivative D at 0. For D different from 0 the quotients Z(s) / s tend to D as s decreases to 0, so the directions of Z(s) tend to D / norm(D), and the escape argument along s decreasing to 0 shows that D / norm(D), hence D, is a generator. For lifts gamma of exp(t X) and beta of exp(t Y), the product curve s -> gamma(s) beta(s) is continuous, passes through the identity, and its image exp(s X) exp(s Y) has derivative X + Y at 0 by the product rule."),
            Node("commutator", "commutator", "Commutator of two generators",
                StatementSource.FromAuthor(CommutatorFormula()),
                DescribeRole.Theorem,
                "Let A be complete, let G be a locally compact topological group and let rho be continuous and injective. If X and Y are one-parameter generators for rho, then so is the commutator X Y - Y X.",
                "Let gamma lift exp(t X) and beta lift exp(t Y). For each real s the curve t -> gamma(s) beta(t) gamma(s)^(-1) is continuous and lifts exp(t exp(s X) Y exp(-s X)), because conjugation by a unit commutes with the exponential series; so the conjugates exp(s X) Y exp(-s X) are generators. Their derivative at s = 0 is X Y - Y X by the product rule. The difference quotients t^(-1) (exp(t X) Y exp(-t X) - Y) are generators by the sum theorem and real multiples, and they tend to X Y - Y X as t tends to 0 with t different from 0. The set of generators is closed, so the limit X Y - Y X is a generator."),
            Node("subalgebra", "generatorSubalgebra", "The Lie subalgebra of generators",
                StatementSource.FromAuthor(SubalgebraFormula()),
                DescribeRole.Definition,
                "Let A be complete, let G be a locally compact topological group and let rho be continuous and injective, with hc a proof of continuity and hi a proof of injectivity. Regard A as a real Lie algebra with the commutator bracket [X, Y] = X Y - Y X. Then generatorSubalgebra(rho, hc, hi) is the Lie subalgebra of A whose carrier is the set setOf of one-parameter generators for rho.",
                "The carrier contains 0, is closed under sums, under real multiples and under the commutator bracket by the preceding theorems, so it is a Lie subalgebra over the real numbers. By the closedness theorem it is moreover a closed subset of A. In the classical closed-subgroup theorem this is the Lie algebra of a closed linear group; here no manifold structure on G is used or asserted."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role,
        params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("one-parameter-generators-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks([.. paragraphs.Select(p => Paragraph(Text(p)))]), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Lam(string name, Formula domain, Formula body) =>
        Seq(Grp(F.Id(name), Colon, domain), Mapsto, Sp, body);
    private static Formula Arrow(Formula x, Formula y) => new Formula.TypeArrow(x, y);

    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Instance(Formula cls) => Seq(OpenBracket, cls, CloseBracket, Comma, Esc);

    private static Formula A => F.Id("A");
    private static Formula G => F.Id("G");
    private static Formula Rho => F.Id("rho");
    private static Formula Hom => Call("MonoidHom", G, Call("Units", A));
    private static Formula Gen(Formula x) => Call("IsOneParameterGenerator", Rho, x);
    private static Formula Smul(Formula c, Formula x) => Call("smul", c, x);
    private static Formula Val(Formula u) => Call("val", u);
    private static Formula Exp(Formula x) => Call("exp", x);

    /// <summary>The algebra and group telescope; <paramref name="complete"/> adds the
    /// completeness, topological-group and local-compactness instances.</summary>
    private static Formula Context(bool complete, Formula body)
    {
        Formula tail = complete
            ? Seq(Instance(Call("CompleteSpace", A)), Instance(Call("IsTopologicalGroup", G)),
                Instance(Call("LocallyCompactSpace", G)), body)
            : body;
        return Disp(ForAll("A", TypeStar, Seq(
            Instance(Call("NormedRing", A)),
            Instance(Call("NormedAlgebra", Reals, A)),
            ForAll("G", TypeStar, Seq(
                Instance(Call("TopologicalSpace", G)),
                Instance(Call("Group", G)),
                tail)))));
    }

    /// <summary>A continuous injective homomorphism followed by <paramref name="body"/>.</summary>
    private static Formula Embedded(Formula body) =>
        ForAll("rho", Hom, Implies(Call("Continuous", Rho), Implies(Call("Injective", Rho), body)));

    private static Formula GeneratorFormula()
    {
        Formula x = F.Id("X"), gamma = F.Id("gamma"), t = F.Id("t");
        Formula lift = Exists("gamma", Arrow(Reals, G), And(
            Call("Continuous", gamma),
            ForAll("t", Reals, Equal(Val(At(Rho, At(gamma, t))), Exp(Smul(t, x))))));
        return Context(false, ForAll("rho", Hom, ForAll("X", A, Iff(Gen(x), lift))));
    }

    private static Formula SmulFormula()
    {
        Formula x = F.Id("X"), c = F.Id("c");
        return Context(false, ForAll("rho", Hom, ForAll("X", A,
            Implies(Gen(x), ForAll("c", Reals, Gen(Smul(c, x)))))));
    }

    private static Formula EscapeFormula()
    {
        Formula g = F.Id("g"), y = F.Id("Y"), x = F.Id("X"), k = F.Id("k");
        Formula direction = Lam("k", Naturals,
            Smul(new Formula.Power(new Formula.Norm(At(y, k)), new Formula.Negate(D(1))), At(y, k)));
        Formula body = ForAll("g", Arrow(Naturals, G), Implies(
            Call("Tendsto", g, Call("atTop"), Call("nhds", D(1))),
            ForAll("Y", Arrow(Naturals, A), Implies(
                Call("Tendsto", y, Call("atTop"), Call("nhds", D(0))),
                Implies(
                    ForAll("k", Naturals, Equal(Val(At(Rho, At(g, k))), Exp(At(y, k)))),
                    ForAll("X", A, Implies(
                        Call("MapClusterPt", x, Call("atTop"), direction),
                        Gen(x))))))));
        return Context(true, Embedded(body));
    }

    private static Formula GeneratorSet =>
        Call("setOf", Lam("X", A, Gen(F.Id("X"))));

    private static Formula ClosedFormula() =>
        Context(true, Embedded(Call("IsClosed", GeneratorSet)));

    private static Formula PairFormula(Formula conclusion)
    {
        Formula x = F.Id("X"), y = F.Id("Y");
        return Context(true, Embedded(ForAll("X", A, ForAll("Y", A,
            Implies(Gen(x), Implies(Gen(y), Gen(conclusion)))))));
    }

    private static Formula AddFormula() =>
        PairFormula(new Formula.Binary(F.Id("X"), FormulaBinaryOperator.Add, F.Id("Y")));

    private static Formula CommutatorFormula()
    {
        Formula x = F.Id("X"), y = F.Id("Y");
        return PairFormula(new Formula.Binary(
            new Formula.Binary(x, FormulaBinaryOperator.Multiply, y),
            FormulaBinaryOperator.Subtract,
            new Formula.Binary(y, FormulaBinaryOperator.Multiply, x)));
    }

    private static Formula SubalgebraFormula()
    {
        Formula hc = F.Id("hc"), hi = F.Id("hi");
        Formula sub = Call("generatorSubalgebra", Rho, hc, hi);
        return Context(true, ForAll("rho", Hom, ForAll("hc", Call("Continuous", Rho),
            ForAll("hi", Call("Injective", Rho), And(
                Rel(sub, FormulaRelationOperator.MemberOf, Call("LieSubalgebra", Reals, A)),
                Equal(Call("carrier", sub), GeneratorSet))))));
    }
}
