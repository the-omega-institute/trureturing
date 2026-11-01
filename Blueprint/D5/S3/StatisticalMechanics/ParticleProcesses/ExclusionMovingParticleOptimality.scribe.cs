using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.ParticleProcesses;

internal sealed class ExclusionMovingParticleOptimalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/chen2017movingparticle");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear occupation observables force every moving-particle constant k to satisfy one at most k times the effective conductance.",
        H("Optimality of the finite-graph moving-particle constant"),
        Blocks(
            Definition("IsConductance", "is-conductance", "Symmetric nonnegative conductances",
                IsConductanceFormula(),
                "A conductance is a nonnegative symmetric real function of two vertices. "
                    + "Zero weights represent absent edges. This expresses the weighted undirected graph "
                    + "of Chen, OctopusMoving_v3.tex, line 111, on a vertex type. "
                    + "The definition also allows disconnected networks and diagonal weights; "
                    + "diagonal pairs contribute zero to both energies."),
            Definition("swap", "swap", "Exchanging two occupations", SwapFormula(),
                "A configuration assigns an element of Fin 2 to each vertex, with zero empty and one occupied. "
                    + "Precomposition with the transposition of x and y exchanges their occupations. "
                    + "When x equals y it fixes the configuration. This is the exchange defined in "
                    + "Chen, OctopusMoving_v3.tex, lines 116–120."),
            Definition("grad", "grad", "The swap gradient", GradFormula(),
                "The gradient is the change in a real observable f after exchanging x and y. "
                    + "Its sign is the value after the exchange minus the original value, as in "
                    + "Chen, OctopusMoving_v3.tex, line 116."),
            Definition("bernoulli", "bernoulli", "Product Bernoulli mass", BernoulliFormula(),
                "Multiply one factor for each vertex: α at an occupied vertex and 1 − α at an empty vertex. "
                    + "For α between zero and one this is the constant-density product Bernoulli probability mass "
                    + "of Chen, OctopusMoving_v3.tex, lines 122–123. The expression is defined for every real α."),
            Definition("expect", "expect", "Expectation of an observable", ExpectFormula(),
                "The dot product sums the value of f at each configuration multiplied by its Bernoulli mass. "
                    + "This is the finite-space version of the expectation notation introduced in "
                    + "Chen, OctopusMoving_v3.tex, line 128. For real α outside the probability interval "
                    + "the same finite weighted sum remains defined."),
            Definition("exclusionEnergy", "exclusion-energy", "The exclusion Dirichlet energy",
                ExclusionEnergyFormula(),
                "Sum each squared swap gradient in expectation, weighted by its conductance. "
                    + "The inner factor one half converts the sum over ordered vertex pairs into a sum "
                    + "over undirected edges. The outer factor one half is the Dirichlet-energy prefactor "
                    + "in Chen, OctopusMoving_v3.tex, lines 125–126."),
            Definition("electricEnergy", "electric-energy", "The electrical Dirichlet energy",
                ElectricEnergyFormula(),
                "For a real potential h, sum each squared potential difference weighted by its conductance. "
                    + "The factor one half removes the duplication of each undirected edge in the ordered-pair sum. "
                    + "This is the electrical energy in Chen, OctopusMoving_v3.tex, lines 160–165."),
            Definition("effectiveConductance", "effective-conductance", "The unit-voltage infimum",
                EffectiveConductanceFormula(),
                "Take the real infimum of electrical energies of potentials equal to one at x and zero at y. "
                    + "For distinct vertices and nonnegative conductances, this set is nonempty and bounded below by zero. "
                    + "It is the reciprocal-effective-resistance expression in Chen, OctopusMoving_v3.tex, "
                    + "line 141. The definition uses the real sInf operation for all arguments, "
                    + "including those for which the unit-voltage conditions are inconsistent."),
            Describe.Lean(
                DescribeId.Create("exclusion-moving-particle-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The converse inequality at every nondegenerate density"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Chen, OctopusMoving_v3.tex, lines 177–179, conjectures optimality on finite weighted graphs "
                        + "and on resistance spaces. Here the finite-graph converse says that if a real constant k "
                        + "bounds the exchange cost by k times the exclusion energy for every real observable, "
                        + "then k times the effective conductance is at least one. "
                        + "The quantifiers include every finite vertex type, every nonnegative symmetric conductance, "
                        + "every pair of distinct vertices and every density strictly between zero and one. "
                        + "For the source's graphs with positive effective conductance, combining this converse "
                        + "with the published upper bound, Theorem 1, lines 131–145, gives the least constant. "
                        + "At zero effective conductance "
                        + "there is no admissible finite real constant. The densities zero and one are excluded: "
                        + "their probability masses are supported on constant configurations, where every swap gradient vanishes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exclusion-moving-particle-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Every admissible constant dominates the resistance"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a real potential h, use the linear occupation observable Fₕ: at ζ its value is "
                            + "the sum over z of h(z) times the natural value of ζ(z), cast to ℝ. "
                            + "For distinct u and w, only these two summands change under the swap. "
                            + "Subtracting gives (h(u) − h(w)) times the difference between the real casts "
                            + "of the occupations at w and u.")),
                    Paragraph(Text(
                        "First compute expectations of products of single-coordinate functions g: "
                            + "the product mass lets the configuration sum factor into the product over z "
                            + "of (1 − α)g(z,0) + αg(z,1). Choosing one coordinate gives expected occupation α; "
                            + "choosing distinct coordinates u and w gives expected product α². "
                            + "Each real occupation has square equal to itself. Expanding the squared occupation "
                            + "difference therefore gives expectation 2α(1 − α).")),
                    Paragraph(Text(
                        "Expectation sends the zero function to zero and commutes with multiplication by a real constant. "
                            + "For u equal to w the swap gradient and the potential difference both vanish. "
                            + "For distinct u and w, square the gradient formula and pull out the squared potential difference. "
                            + "Thus for all u and w the expected squared gradient of Fₕ is "
                            + "2α(1 − α)(h(u) − h(w))². Substitution into the ordered-pair sum gives "
                            + "exclusionEnergy(c,α,Fₕ) = α(1 − α) electricEnergy(c,h). "
                            + "If h(x) = 1 and h(y) = 0, half the expected squared x,y-gradient is α(1 − α).")),
                    Paragraph(Text(
                        "Nonnegative conductances make every electrical energy nonnegative. "
                            + "For distinct x and y the potential equal to one at x and zero elsewhere "
                            + "satisfies the unit-voltage conditions, so the feasible energy set is nonempty. "
                            + "Suppose 1 ≤ k electricEnergy(c,h) for every feasible h. "
                            + "Testing any such potential shows k > 0: otherwise its nonnegative energy "
                            + "would make the right side nonpositive. Division by k shows that 1/k bounds "
                            + "every feasible energy from below. The defining infimum is consequently "
                            + "at least 1/k, and multiplication by k gives 1 ≤ k effectiveConductance(c,x,y).")),
                    Paragraph(Text(
                        "Finally fix the finite conductance network, distinct x and y, density 0 < α < 1 "
                            + "and an admissible k. For each unit-voltage potential h, apply the assumed "
                            + "moving-particle bound to Fₕ. The two identities give "
                            + "α(1 − α) ≤ k α(1 − α) electricEnergy(c,h). "
                            + "Since α(1 − α) is positive, cancellation yields "
                            + "1 ≤ k electricEnergy(c,h) for every feasible h. The infimum argument proves the conclusion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chen-2017-exclusion-moving-particle-optimality"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string name, string id, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("exclusion-moving-particle-" + id),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula IsConductanceFormula()
    {
        Formula nonnegative = All("u", X("v"), All("w", X("v"),
            LE(RealZero(), At(X("c"), X("u"), X("w")))));
        Formula symmetric = All("u", X("v"), All("w", X("v"),
            Equal(At(X("c"), X("u"), X("w")), At(X("c"), X("w"), X("u")))));
        return Vertices(All("c", ConductanceType(),
            Equivalence(Call("IsConductance", X("c")), Conjunction(nonnegative, symmetric))));
    }

    private static Formula SwapFormula() => Vertices(
        All("x", X("v"), All("y", X("v"), All("ζ", States(),
            Equal(Typed(Call("swap", X("x"), X("y"), X("ζ")), States()),
                At(Qualified("Function", "comp"), X("ζ"),
                    At(Qualified("Equiv", "toFun"),
                        At(Qualified("Equiv", "swap"), X("x"), X("y")))))))), equality: true);

    private static Formula GradFormula() => Vertices(
        All("x", X("v"), All("y", X("v"), All("f", Observables(), All("ζ", States(),
            Equal(Typed(Call("grad", X("x"), X("y"), X("f"), X("ζ")), Reals()),
                Subtract(At(X("f"), Call("swap", X("x"), X("y"), X("ζ"))), At(X("f"), X("ζ")))))))),
        equality: true);

    private static Formula BernoulliFormula() => Vertices(
        All("α", Reals(), All("ζ", States(),
            Equal(Typed(Call("bernoulli", X("α"), X("ζ")), Reals()),
                ProductOver("z", X("v"), At(Qualified("ite"),
                    Equal(At(X("ζ"), X("z")), Typed(D(1), FinTwo())),
                    X("α"), Subtract(RealOne(), X("α"))))))), finite: true);

    private static Formula ExpectFormula() => Vertices(
        All("α", Reals(), All("f", Observables(),
            Equal(Typed(Call("expect", X("α"), X("f")), Reals()),
                At(Qualified("dotProduct"), Call("bernoulli", X("α")), X("f"))))), finite: true);

    private static Formula ExclusionEnergyFormula()
    {
        Formula moment = Call("expect", X("α"), LambdaOf("ζ", States(),
            Square(Call("grad", X("u"), X("w"), X("f"), X("ζ")))));
        Formula total = SumOver("u", X("v"), SumOver("w", X("v"),
            Multiply(At(X("c"), X("u"), X("w")), moment)));
        Formula body = Equal(Typed(Call("exclusionEnergy", X("c"), X("α"), X("f")), Reals()),
            Multiply(Half(), Multiply(Half(), total)));
        return Vertices(All("c", ConductanceType(), All("α", Reals(), All("f", Observables(), body))),
            finite: true, equality: true);
    }

    private static Formula ElectricEnergyFormula() => Vertices(
        All("c", ConductanceType(), All("h", Potentials(),
            Equal(Typed(Call("electricEnergy", X("c"), X("h")), Reals()),
                Multiply(Half(), SumOver("u", X("v"), SumOver("w", X("v"),
                    Multiply(At(X("c"), X("u"), X("w")),
                        Square(Subtract(At(X("h"), X("u")), At(X("h"), X("w"))))))))))),
        finite: true);

    private static Formula EffectiveConductanceFormula()
    {
        Formula feasible = Some("h", Potentials(), Conjunction(
            Equal(At(X("h"), X("x")), RealOne()), Conjunction(
                Equal(At(X("h"), X("y")), RealZero()),
                Equal(X("e"), Call("electricEnergy", X("c"), X("h"))))));
        Formula energies = Seq(OpenBrace, Typed(X("e"), Reals()), Sp, Mid, Sp, feasible, CloseBrace);
        return Vertices(All("c", ConductanceType(), All("x", X("v"), All("y", X("v"),
            Equal(Typed(Call("effectiveConductance", X("c"), X("x"), X("y")), Reals()),
                At(Qualified("sInf"), energies))))), finite: true);
    }

    private static Formula ClaimBody()
    {
        Formula admissible = All("f", Observables(),
            LE(Multiply(Half(), Call("expect", X("α"), LambdaOf("ζ", States(),
                    Square(Call("grad", X("x"), X("y"), X("f"), X("ζ")))))),
                Multiply(X("k"), Call("exclusionEnergy", X("c"), X("α"), X("f")))));
        Formula body = Implication(admissible,
            LE(RealOne(), Multiply(X("k"), Call("effectiveConductance", X("c"), X("x"), X("y")))));
        body = All("k", Reals(), body);
        body = All("α", Reals(), Implication(LT(RealZero(), X("α")),
            Implication(LT(X("α"), RealOne()), body)));
        body = All("x", X("v"), All("y", X("v"), Implication(NotEqual(X("x"), X("y")), body)));
        body = All("c", ConductanceType(), Implication(Call("IsConductance", X("c")), body));
        return Vertices(body, finite: true, equality: true);
    }

    private static Formula Vertices(Formula body, bool finite = false, bool equality = false)
    {
        if (equality) body = Instance(At(Qualified("DecidableEq"), X("v")), body);
        if (finite) body = Instance(At(Qualified("Fintype"), X("v")), body);
        return All("v", Qualified("Type"), body);
    }

    private static Formula X(string name) => name switch
    {
        "α" => Alpha,
        "ζ" => Zeta,
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified(name);
    private static Formula Call(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealZero() => Typed(D(0), Reals());
    private static Formula RealOne() => Typed(D(1), Reals());
    private static Formula Half() => new Formula.Fraction(RealOne(), Typed(D(2), Reals()));
    private static Formula FinTwo() => At(Qualified("Fin"), D(2));
    private static Formula States() => Arrow(X("v"), FinTwo());
    private static Formula Potentials() => Arrow(X("v"), Reals());
    private static Formula Observables() => Arrow(States(), Reals());
    private static Formula ConductanceType() => Arrow(X("v"), Arrow(X("v"), Reals()));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula ProductOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), Typed(D(2), Naturals()));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
}
