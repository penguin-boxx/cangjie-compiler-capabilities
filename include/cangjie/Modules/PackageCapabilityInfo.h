// Copyright (c) Huawei Technologies Co., Ltd. 2026. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
//
// See https://cangjie-lang.cn/pages/LICENSE for license information.

/**
 * @file
 *
 * This file declares what a loaded package's capability metadata says about it.
 */

#ifndef CANGJIE_MODULES_PACKAGECAPABILITYINFO_H
#define CANGJIE_MODULES_PACKAGECAPABILITYINFO_H

#include <cstdint>

namespace Cangjie {
/**
 * Checked exceptions: what a loaded package's capability metadata is worth to its consumers.
 * The defaults describe a package produced before the feature existed: nothing recorded, so an
 * empty capability list means "unknown", not "requires nothing".
 */
struct PackageCapabilityInfo {
    enum class Level : uint8_t { OFF, WARN, ERROR };
    Level level{Level::OFF};         /**< Severity capability checking ran at, 'OFF' if it did not. */
    bool effectsEnabled{false};      /**< Whether effect handlers were enabled for the package. */
    bool recordsCapabilities{false}; /**< Whether the package carries capability metadata at all. */
};
} // namespace Cangjie

#endif // CANGJIE_MODULES_PACKAGECAPABILITYINFO_H
