using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class OneStepSchurGainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A generated observation direction gives its exact normalized distance gain.",
        H("One-Step Schur Gain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("generated-direction-gives-normalized-distance-gain"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/OneStepSchurGain.one_step_schur_gain"),
                H("A generated direction gives its normalized distance gain"),
                StatementSource.FromAuthor(GainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a finite-dimensional observation subspace of a real or complex "
                        + "inner-product space. Construct the residual of a new generator by "
                        + "projecting it onto the orthogonal complement of S, and construct the "
                        + "next observation space by adjoining the generator to S.")),
                    Paragraph(Text(
                        "If the constructed residual is nonzero, the squared distance drop for "
                        + "any target is its squared coupling with the residual divided by the "
                        + "residual's squared norm. If the residual is zero, adjoining the "
                        + "generator does not change the target's distance.")),
                    Paragraph(Text(
                        "Pinned Mathlib provides the exact projection identities "
                        + "Submodule.starProjection_singleton, "
                        + "Submodule.starProjection_minimal, "
                        + "Submodule.starProjection_orthogonal_val, and "
                        + "Submodule.norm_sq_eq_add_norm_sq_starProjection. The proof applies "
                        + "them on the source-constructed spaces. Repository searches found "
                        + "related nested-space and nonzero gain theorems, but no declaration "
                        + "with both generated-space cases.")),
                    Paragraph(Text(
                        "This formalizes theorem 29.8. Both case clauses are public; the result "
                        + "does not assert convergence of a sequence of observation spaces."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula>
        {
            Operatorname,
            Grp(F.Id(name)),
            Open,
        };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula GainFormula()
    {
        Formula field = F.Id("K");
        Formula space = F.Id("V");
        Formula oldSpace = F.Id("S");
        Formula target = F.Id("target");
        Formula generator = F.Id("generator");
        Formula residual = F.Id("residual");
        Formula next = F.Id("next");
        Formula complement = Seq(oldSpace, Caret, Grp(Perp));
        Formula projection = Seq(
            Operatorname, Grp(F.Id("proj")), Underscore, Grp(complement), Open, generator, Close);
        Formula inner = Seq(Langle, Sp, target, Comma, Sp, residual, Sp, Rangle);
        Formula absoluteInner = Seq(Lvert, Sp, inner, Sp, Rvert);
        Formula residualNorm = Seq(Vert, Sp, residual, Sp, Vert);
        Formula oldDistanceSquared = Seq(Call("dist", target, oldSpace), Caret, Grp(D(2)));
        Formula nextDistanceSquared = Seq(Call("dist", target, next), Caret, Grp(D(2)));

        return Disp(Seq(
            Forall, Sp, field, Colon, Sp, Operatorname, Grp(F.Id("RCLike")), Comma, Esc,
            Forall, Sp, space, Colon, Sp, Call("InnerProductSpace", field), Comma, Esc,
            Forall, Sp, oldSpace, InMacro, Sp,
            Call("FiniteDimensionalSubmodule", field, space), Comma, Esc,
            Forall, Sp, target, Comma, Sp, generator, InMacro, Sp, space, Comma, Esc,
            residual, Sp, Eq, Sp, projection, Comma, Sp,
            next, Sp, Eq, Sp, Call("sup", oldSpace, Call("span", generator)), Comma, Esc,
            Open, residual, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            oldDistanceSquared, Sp, Minus, Sp, nextDistanceSquared, Sp, Eq, Sp,
            Frac, Grp(absoluteInner, Caret, Grp(D(2))),
            Grp(residualNorm, Caret, Grp(D(2))), Close, Sp, Land, Esc,
            Open, residual, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            Call("dist", target, next), Sp, Eq, Sp, Call("dist", target, oldSpace), Close, Dot));
    }
}
