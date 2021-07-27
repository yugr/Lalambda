---
theme: gaia
_class: lead
paginate: true
backgroundColor: #fff
backgroundImage: url('https://marp.app/assets/hero-background.jpg')

---
<style>
footer {
    height: 200px;
    margin-bottom: -80px;
}
</style>

# **Samsung Moscow SoC team**

---

# Про System-on-Chip team

Команда System-on-Chip:
  * существует 10+ лет
  * разрабатывает компиляторы и связанные проекты (статический и динамический анализ и другой тулинг)
  * используемые технологии: in-house, Clang/LLVM, GCC

---

# Что классно

* State-of-the-art технологии
* Возможность "потрогать" результат руками
* Дружелюбный коллектив
* Есть у кого учиться

---

# Достижения (1)

* Разработка двух поколений компилятора для нейросетевого ускорителя (в high-end-телефонах Samsung Galaxy)
  * [Ускоряем нейросеть на уровне железа: интервью с разработчиком компиляторов](https://habr.com/ru/company/samsung/blog/549006/)
* Поддержка фронтенда OpenACC в компиляторе GCC
* Разработка компилятора для DSP-процессоров
  * [DSP-процессоры: назначение и особенности](https://habr.com/ru/company/samsung/blog/564282/)

---

# Достижения (2)

* Поддержка межмодульного анализа в Clang Static Analyzer
  * [2016 LLVM Developers' Meeting: A. Sidorin "Summary-based inter-unit analysis for CSA](https://www.youtube.com/watch?v=jbLkZ82mYE4)
* Поддержка новых фич в AddressSanitizer LLVM и GCC (continue-after-error, порт на ARM, etc.)
  * [GCC devmeeting 2017: Applying GNU GCC Address Sanitizer to whole Linux distribution](https://slideslive.com/38902439/applying-gnu-gcc-address-sanitizer-to-whole-linux-distribution)
  * [GCC devmeeting 2019: Annotating std::string with AddressSanitizer](https://gcc.gnu.org/wiki/cauldron2019#cauldron2019talks.Annotating_std_string_with_AddressSanitizer)

---

# Достижения (3)

* NDA :(

---

# Планы

* Компиляторы для application-specific ускорителей
  * ["The Future of Computing: Domain-Specific Accelerators" William Dally](https://www.youtube.com/watch?v=fnd05AeeFN4)
* Верификация (может быть...)

---

# Кого мы ищем

NPU-компилятор:
  * NPU Compiler Developer for Exynos AI Accelerator (https://hh.ru/vacancy/42341825)

High-performance computing:
  * [GPU performance engineer](https://hh.ru/vacancy/44907512)
  * можно без опыта если знаете и умеете в CUDA и MPI

Разработчик DSP-компиляторов:
  * пока неактивна :(

---

# Что надо будет делать (1)

* Кодить на C++, Python, shell (редко asm)
* Отлаживаться: понять почему _опять_ упал Jenkins, копаться в логах, читать ассемблер, разбиратся в спеках по микроархитектуре девайса, etc.
* Ревуить чужой код
* Общаться (S. Korea, China, US, Israel)

---

# Что надо будет делать (2)

* Читать новые (и старые) статьи по предметной области
* Исследовать и править open-source код (LLVM, GCC, ROCm, etc.)
  * можно коммитить в open-source :)
  * если есть время :(

---

# Зачем мне это?

* Делать современный тулинг в высокопрофессиональной международной команде
* Знакомиться с cutting-edge технологиями компиляции и HW-ускорения

---

# Задать вопросы ???

TG @the\_real\_yugr
