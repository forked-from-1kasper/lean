#include "kernel/hott/hott.h"
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include "kernel/abstract_type_context.h"
#include "kernel/kernel_exception.h"

namespace lean {

static name * g_hott_extension = nullptr;
static name * g_fibrant        = nullptr;

struct hott_env_ext : public environment_extension {
    bool m_initialized;
    hott_env_ext():m_initialized(false){}
};

struct hott_env_ext_reg {
    unsigned m_ext_id;
    hott_env_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<hott_env_ext>()); }
};

static hott_env_ext_reg * g_ext = nullptr;

static hott_env_ext const & get_extension(environment const & env) {
    return static_cast<hott_env_ext const &>(env.get_extension(g_ext->m_ext_id));
}

static environment update(environment const & env, hott_env_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<hott_env_ext>(ext));
}

static environment add_constant(environment const & env, name const & n, std::initializer_list<name> lvls, expr const & type) {
    auto cd = check(env, mk_constant_assumption(n, level_param_names(lvls), type));
    return env.add(cd);
}

environment declare_hott(environment const & env) {
    environment new_env = env;

    name u_name("u");
    level u = mk_param_univ(u_name);
    expr Type_u = mk_sort(mk_succ(u));
    expr Prop   = mk_Prop();

    /* constant {u} fibrant : Type u → Prop */
    new_env = add_constant(new_env, *g_fibrant, {u_name}, mk_arrow(Type_u, Prop));

    hott_env_ext ext = get_extension(env);
    if (ext.m_initialized)
        throw exception("failed to initialize HoTT module, already initialized");
    ext.m_initialized = true;
    return update(new_env, ext);
}

optional<expr> hott_normalizer_extension::operator()(expr const & e, abstract_type_context & ctx) const {
    return none_expr();
}

optional<expr> hott_normalizer_extension::is_stuck(expr const & e, abstract_type_context & ctx) const {
    return none_expr();
}

bool hott_normalizer_extension::supports(name const & feature) const {
    return feature == *g_hott_extension;
}

bool hott_normalizer_extension::is_recursor(environment const &, name const & n) const {
    return false;
}

bool hott_normalizer_extension::is_builtin(environment const & env, name const & n) const {
    if (!get_extension(env).m_initialized) return false;
    return n == *g_fibrant;
}

void initialize_hott_module() {
    g_hott_extension = new name("hott_extension");
    g_ext            = new hott_env_ext_reg();
    g_fibrant        = new name("fibrant");
}

void finalize_hott_module() {
    delete g_fibrant;
    delete g_ext;
    delete g_hott_extension;
}

}