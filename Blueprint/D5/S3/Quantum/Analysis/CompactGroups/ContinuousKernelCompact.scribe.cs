using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.CompactGroups;

internal sealed class ContinuousKernelCompactDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/CompactGroups/ContinuousKernelCompact.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For compact spaces X and Y, a finite measure on Y and a continuous kernel on X x Y with real or complex values, the integral operator of the kernel is a compact operator from the Lebesgue space of exponent at least one into the continuous functions on X.",
        H("Compact Integral Operators with a Continuous Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("continuous-kernel-compact-operator"),
                DeclarationHandle.Create(Prefix + "exists_isCompactOperator_kernel"),
                H("The integral operator of a continuous kernel is compact"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let X and Y be compact topological spaces, let Y carry a measurable structure containing its open sets, and let m be a finite measure on Y. The scalar field k is a real or complex field in the sense of the class RCLike (the real numbers, the complex numbers, or a field carrying the same structure), the exponent p lies in [1, infinity], and K is a continuous function on the product X x Y with values in k. The statement provides a continuous k-linear map T from the Lebesgue space Lp(k, p, m) into the space C(X, k) of continuous functions on X with the supremum norm, such that T is a compact operator and, for every f in Lp(k, p, m) and every x in X, the value of T(f) at x is the integral of K(x, y) f(y) over y with respect to m. The integral does not depend on the representative of f, and T(f) is continuous on X.")),
                    Paragraph(Text("Since m is finite and p is at least one, every f in Lp(k, p, m) is integrable, and the integral of the absolute value of f is at most C times the norm of f, where C is the real number m(Y) raised to the power 1 - 1/p. Pairing f with a continuous function g on Y is therefore bounded by the supremum norm of g times C times the norm of f. This gives the pointwise bound: the absolute value of T(f)(x) is at most the supremum of the absolute value of K times C times the norm of f, so T is bounded with operator norm at most that product. It also gives, for points x and x' of X, a bound for the absolute value of T(f)(x) - T(f)(x') by the supremum over y of the absolute value of K(x, y) - K(x', y), times C times the norm of f. The map sending x to the section K(x, -) is continuous from X into C(Y, k) with the supremum norm, because K is continuous on the compact space X x Y.")),
                    Paragraph(Text("Hence the image of the unit ball of Lp(k, p, m) under T is uniformly bounded and equicontinuous on the compact space X, with values in a compact disc of k. The Arzela-Ascoli theorem gives a compact subset of C(X, k) containing this image, and T is a compact operator. This is the classical compactness of integral operators with a continuous kernel, obtained by the standard argument.")),
                    Paragraph(Text("Continuity of the kernel is used twice, for the continuity of T(f) and for the equicontinuity of the image of the unit ball; finiteness of the measure is used for the integrability of Lp functions and the bound C. Compactness of X and Y makes K bounded and its sections uniformly continuous in x. On the one-point space Y with the unit point mass, the operator sends the constant function 1 to the function whose value at x is K(x, y0), where y0 is the point, so the values of T recover the kernel itself."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Instance(Formula cls) => Seq(OpenBracket, cls, CloseBracket, Comma, Esc);
    private static Formula ExtendedNonnegative => Seq(OpenBracket, D(0), Comma, Sp, Infty, CloseBracket);

    private static Formula KernelFormula()
    {
        Formula x = F.Id("X"), y = F.Id("Y"), k = F.Id("k"), m = F.Id("m"), p = F.Id("p");
        Formula kernel = F.Id("K"), op = F.Id("T"), f = F.Id("f"), pt = F.Id("x"), var = F.Id("y");
        Formula lp = Call("Lp", k, p, m);
        Formula cx = Call("C", x, k);
        Formula product = Seq(x, Sp, Times, Sp, y);
        Formula integral = Seq(Int, Sp, At(kernel, Seq(pt, Comma, Sp, var)), Sp, Cdot, Sp, At(f, var),
            Sp, Thin, Mathrm, Grp(F.Id("d")), At(m, var));
        Formula values = ForAll("f", lp, ForAll("x", x, Equal(At(At(op, f), pt), integral)));
        Formula conclusion = Exists("T", Call("ContinuousLinearMap", k, lp, cx),
            And(Call("IsCompactOperator", op), values));
        return Disp(ForAll("X", TypeStar, ForAll("Y", TypeStar, ForAll("k", TypeStar, Seq(
            Instance(Call("TopologicalSpace", x)),
            Instance(Call("CompactSpace", x)),
            Instance(Call("TopologicalSpace", y)),
            Instance(Call("CompactSpace", y)),
            Instance(Call("MeasurableSpace", y)),
            Instance(Call("OpensMeasurableSpace", y)),
            Instance(Call("RCLike", k)),
            ForAll("m", Call("Measure", y), Seq(
                Instance(Call("IsFiniteMeasure", m)),
                ForAll("p", ExtendedNonnegative, Seq(
                    Instance(Call("Fact", Rel(D(1), FormulaRelationOperator.LessThanOrEqual, p))),
                    ForAll("K", Call("C", product, k), conclusion))))))))));
    }
}
