#pragma once
#include "kernel/normalizer_extension.h"

namespace lean {

class hott_normalizer_extension : public normalizer_extension {
public:
    virtual optional<expr> operator()(expr const & e, abstract_type_context & ctx) const;
    virtual optional<expr> is_stuck(expr const & e, abstract_type_context & ctx) const;
    virtual bool supports(name const & feature) const;
    virtual bool is_recursor(environment const & env, name const & n) const;
    virtual bool is_builtin(environment const & env, name const & n) const;
};

environment declare_hott(environment const & env);
void initialize_hott_module();
void finalize_hott_module();

}